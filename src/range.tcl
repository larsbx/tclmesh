# Range certificates (spec/TclMesh/Range.lean).
#
# A `w`-bit homomorphic integer wraps modulo 2^w and cannot detect overflow.
# `emit` computes the least range of every node by interval arithmetic from
# the declared input ranges (`{cipher int range LO HI}`; the whole word when
# none is declared; [0, 1] for bool); `check` validates any certificate and
# returns its violations (empty when accepted). When the proved Lean checker
# accepts, no intermediate wraps: wrapped evaluation equals exact evaluation
# (`check_sound`). This checker must agree with it (tools/views.tcl).
#
# The arithmetic is the contract of `finite_exact/word_range.mojo` in
# larsbx/finite-math-kernels; its corpus, pinned in UPSTREAM.toml, is
# replayed against `op` (tests/range.test).
#
# Profiles whose semantics is `int<W>-checked` evaluate only circuits whose
# least certificate is accepted at width W, on inputs inside their declared
# ranges (`require`).

namespace eval ::tclmesh::range {
    namespace export emit check op require word
    namespace ensemble create

    # Words after the operation, for every range-checked operation.
    variable arity {
        constant 1 input 1 negate 1 not 1 select 3
        add 2 subtract 2 multiply 2 equal 2 less-than 2 less-or-equal 2
        greater-than 2 greater-or-equal 2 and 2 or 2
    }
}

# The only integer spelling accepted: -?(0|[1-9][0-9]*), without -0.
proc ::tclmesh::range::_int {text} {
    expr {[regexp {^-?(0|[1-9][0-9]*)$} $text] && $text ne "-0"}
}

proc ::tclmesh::range::word {width} {
    if {![_int $width] || $width < 1 || $width > 32} {
        return -code error -errorcode [list TCLMESH RANGE INVALID_WIDTH $width] \
            "word width must be an integer in 1..32"
    }
    set half [expr {1 << ($width - 1)}]
    list [expr {-$half}] [expr {$half - 1}]
}

proc ::tclmesh::range::_within {inner outer} {
    lassign $inner lo hi
    lassign $outer olo ohi
    expr {$olo <= $lo && $hi <= $ohi}
}

proc ::tclmesh::range::_min {args} { tcl::mathfunc::min {*}$args }
proc ::tclmesh::range::_max {args} { tcl::mathfunc::max {*}$args }

# Least range of an operation on operand ranges (natural interval extension),
# before any word check.
proc ::tclmesh::range::_extend {op ranges} {
    lassign $ranges p q
    lassign $p plo phi
    lassign $q qlo qhi
    switch -- $op {
        add      { list [expr {$plo + $qlo}] [expr {$phi + $qhi}] }
        subtract { list [expr {$plo - $qhi}] [expr {$phi - $qlo}] }
        negate   { list [expr {-$phi}] [expr {-$plo}] }
        multiply {
            set corners [list [expr {$plo * $qlo}] [expr {$plo * $qhi}] \
                [expr {$phi * $qlo}] [expr {$phi * $qhi}]]
            list [_min {*}$corners] [_max {*}$corners]
        }
        select   { list [_min $plo $qlo] [_max $phi $qhi] }
        default  { list 0 1 }
    }
}

# A declared input range, or {} when the descriptor admits none.
proc ::tclmesh::range::_input {descriptor width} {
    set words [lrange $descriptor 1 end]
    if {$words eq "int"} {
        return [word $width]
    }
    if {$words eq "bool"} {
        return {0 1}
    }
    if {[llength $words] == 4 && [lrange $words 0 1] eq {int range}} {
        lassign [lrange $words 2 3] lo hi
        if {[_int $lo] && [_int $hi]} {
            return [list $lo $hi]
        }
    }
    return {}
}

# {op operands} for a range-checked node; {} for any other (lists, lookups,
# polynomials, wrong arity).
proc ::tclmesh::range::_shape {node} {
    variable arity
    set op [lindex $node 0]
    if {![dict exists $arity $op] || [llength $node] != [dict get $arity $op] + 1} {
        return {}
    }
    list $op [lrange $node 1 end]
}

proc ::tclmesh::range::_least {circuit id width memoVar} {
    upvar 1 $memoVar memo
    if {[dict exists $memo $id]} {
        return [dict get $memo $id]
    }
    dict set memo $id {}
    set result {}
    if {[dict exists $circuit nodes $id]} {
        set node [dict get $circuit nodes $id]
        set shape [_shape $node]
        if {$shape ne ""} {
            lassign $shape op operands
            switch -- $op {
                input {
                    set name [lindex $operands 0]
                    if {[dict exists $circuit inputs $name]} {
                        set result [_input [dict get $circuit inputs $name] $width]
                    }
                }
                constant {
                    set k [lindex $operands 0]
                    if {[_int $k]} {
                        set result [list $k $k]
                    }
                }
                default {
                    set ranges [lmap ref $operands {_least $circuit $ref $width memo}]
                    if {"" ni $ranges} {
                        if {$op eq "select"} {
                            set ranges [lrange $ranges 1 2]
                        }
                        set result [_extend $op $ranges]
                    }
                }
            }
        }
    }
    dict set memo $id $result
    return $result
}

# The least certificate: {id {lo hi} ...} for every node that has a least
# range. Whether it fits the word is `check`'s decision.
proc ::tclmesh::range::emit {circuit {width 32}} {
    set circuit [::tclmesh::private::validate $circuit]
    word $width
    set memo {}
    set ranges {}
    foreach id [dict keys [dict get $circuit nodes]] {
        set r [_least $circuit $id $width memo]
        if {$r ne ""} {
            dict set ranges $id $r
        }
    }
    return $ranges
}

proc ::tclmesh::range::_valid {r} {
    expr {[llength $r] == 2 && [_int [lindex $r 0]] && [_int [lindex $r 1]]}
}

# Violations of a certificate {id {lo hi} ...}, in node order; empty when the
# certificate is accepted.
proc ::tclmesh::range::check {circuit cert {width 32}} {
    set bounds [word $width]
    set violations {}
    dict for {id r} $cert {
        if {![_valid $r] || ![_within $r $bounds]} {
            lappend violations [list outside-word $id]
        }
    }
    dict for {id node} [dict get $circuit nodes] {
        if {![dict exists $cert $id] || ![_valid [dict get $cert $id]]} {
            lappend violations [list unranged $id]
            continue
        }
        set r [dict get $cert $id]
        set shape [_shape $node]
        if {$shape eq ""} {
            lappend violations [list unsupported $id]
            continue
        }
        lassign $shape op operands
        switch -- $op {
            input {
                set name [lindex $operands 0]
                set declared {}
                if {[dict exists $circuit inputs $name]} {
                    set declared [_input [dict get $circuit inputs $name] $width]
                }
                set ok [expr {$declared ne "" && [_within $declared $r]}]
            }
            constant {
                set k [lindex $operands 0]
                set ok [expr {[_int $k] && [_within [list $k $k] $r]}]
            }
            default {
                set ranges {}
                foreach ref $operands {
                    if {![dict exists $cert $ref] || ![_valid [dict get $cert $ref]]} {
                        lappend violations [list unranged-operand $id $ref]
                        set ranges {}
                        break
                    }
                    lappend ranges [dict get $cert $ref]
                }
                if {$ranges eq ""} {
                    continue
                }
                switch -- $op {
                    select {
                        set ok [expr {[_within [lindex $ranges 1] $r] && [_within [lindex $ranges 2] $r]}]
                    }
                    default {
                        set ok [_within [_extend $op $ranges] $r]
                    }
                }
            }
        }
        if {!$ok} {
            lappend violations [list under-range $id]
        }
    }
    return $violations
}

# One operation of the word-range contract (finite_exact/word_range.mojo):
# OP in add subtract multiply negate hull, on ranges {lo hi}; the result, or
# `refused` when an operand is refused or the result leaves the word.
proc ::tclmesh::range::op {op width args} {
    set bounds [word $width]
    if {"refused" in $args} {
        return refused
    }
    foreach r $args {
        if {![_valid $r] || [lindex $r 0] > [lindex $r 1] || ![_within $r $bounds]} {
            return refused
        }
    }
    set r [_extend [dict get {add add sub subtract mul multiply neg negate hull select} $op] $args]
    expr {[_within $r $bounds] ? $r : "refused"}
}

# Admit a circuit for evaluation at width W: its least certificate must be
# accepted. Returns the certificate.
proc ::tclmesh::range::require {circuit width} {
    set cert [emit $circuit $width]
    set violations [check $circuit $cert $width]
    if {$violations ne ""} {
        return -code error -errorcode [list TCLMESH PRIVATE RANGE REJECTED $violations] \
            "circuit may overflow int$width: $violations"
    }
    return $cert
}

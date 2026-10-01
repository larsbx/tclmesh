set here [file dirname [file normalize [info script]]]
set root [file dirname $here]
lappend auto_path $root

package require tclmesh 0.3.0

tclmesh private profile define differential-reference [dict create     backend plaintext     semantics exact-integer     parameters [dict create mode reference]     allow_decrypt true]

set circuit [tclmesh private circuit plus-one     [dict create x {cipher int}]     [dict create y {cipher int}]     [dict create         x [tclmesh private node input x]         one [tclmesh private node constant 1]         y [tclmesh private node add x one]]     [dict create output_nodes [dict create y y]]]

set differential [tclmesh private differential     differential-reference     $circuit     [dict create x 41]]

tclmesh private profile define threshold-reference [dict create     backend plaintext     semantics exact-integer     parameters [dict create mode reference]     allow_decrypt false]

set handle [tclmesh private encrypt threshold-reference int 42]

set request [tclmesh release request     $handle     demo-release     2     {holder:a holder:b holder:c}     [dict create purpose demo]]

set release_id [dict get $request id]
tclmesh release contribute $release_id holder:a share-a
tclmesh release contribute $release_id holder:b share-b
set released [tclmesh release combine $release_id]

puts "differential:[dict get $differential match]|released:[dict get $released result]"

"""Generate P0 toy-BFV transcripts and replay them through the P1 BEAM process."""
import random
import subprocess
import tempfile
from pathlib import Path

import q45_oracle as oracle

SOURCE = Path(__file__).resolve().parents[1] / "experiments" / "threshold_q45"
COEFFICIENT_BYTES = 16


def encode(*polynomials):
    return b"".join(
        coefficient.to_bytes(COEFFICIENT_BYTES, "big")
        for polynomial in polynomials
        for coefficient in polynomial
    ).hex()


def write_transcripts(path):
    with path.open("w", encoding="ascii") as stream:
        for seed in oracle.SEEDS:
            rng = random.Random(f"P1 replay:{seed}")
            ctx = oracle.keygen(rng)
            shares = oracle.replicate(ctx.s, rng)
            for mask, bits in enumerate(oracle.INPUTS):
                inputs = [oracle.encrypt(ctx, bit, rng) for bit in bits]
                ciphertext = oracle.e4(oracle.ct_add, lambda a, b: oracle.ct_mul(ctx, a, b), inputs)
                expected = oracle.reference(bits)
                for quorum in oracle.QUORUMS:
                    (omitted,) = set(oracle.PARTIES) - quorum
                    parts = oracle.partials(shares, quorum, ciphertext[1], rng, oracle.SMUDGE_BITS)
                    decoded = oracle.combine(ciphertext, parts)
                    if decoded != (expected,) + (0,) * (oracle.N - 1):
                        raise ValueError(f"P0 reconstruction mismatch: {seed:#x}/{mask}/{omitted}")
                    fields = [
                        str(seed), str(mask), str(omitted), str(decoded[0]),
                        *(encode(*value) for value in inputs), encode(*ciphertext),
                        *(encode(parts[party]) for party in sorted(quorum)),
                    ]
                    stream.write("\t".join(fields) + "\n")


def main():
    with tempfile.TemporaryDirectory(prefix="q45-toy-replay-") as tmp:
        directory = Path(tmp)
        write_transcripts(directory / "transcripts.tsv")
        subprocess.run(
            ["erlc", "-Werror", "-o", directory,
             SOURCE / "q45_ceremony.erl", SOURCE / "q45_toy_replay.erl"],
            check=True, timeout=30,
        )
        subprocess.run(
            ["erl", "-noshell", "-pa", directory, "-eval",
             'ok = q45_toy_replay:run("transcripts.tsv"), halt(0).'],
            cwd=directory, check=True, timeout=60,
        )


if __name__ == "__main__":
    main()

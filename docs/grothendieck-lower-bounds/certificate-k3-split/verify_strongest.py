"""Verify the strongest matrix and regenerate the exhaustive reference band."""

import argparse, hashlib, json, struct, subprocess, tempfile
from pathlib import Path
from construction.rebuild import rebuild
from cover import caps, matrix
from band_certificate import signed, check_scores

ROOT = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise RuntimeError("Run Python without -O so the certificate checks are enabled.")
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--threads", type=int, default=4)
    p.add_argument("--vectors-only", action="store_true")
    p.add_argument("--portable", action="store_true")
    p.add_argument("--compiler", default="g++")
    p.add_argument("--scratch", type=Path)
    opt = p.parse_args()
    assert 1 <= opt.threads <= 256
    for f, h in json.loads((ROOT / "SHA256SUMS.json").read_text()).items():
        assert hashlib.sha256((ROOT / f).read_bytes()).hexdigest() == h, f
    base = matrix(ROOT / "base.txt")
    first = rebuild()
    I = list(map(int, (ROOT / "split_rows.txt").read_text().split()))
    sym = matrix(ROOT / "symmetry.txt")
    d = ROOT / "second"
    w = json.loads((d / "witness.json").read_text())
    saved = d / "band.bin"
    witness, M, center, ratio = signed(w, ROOT, base, first, I, sym, saved)
    print(
        "Checked rank-three vectors, exact numerator, residual norm, stored sign scores and the attaining signing.",
        flush=True,
    )
    if (d / "vector_room.json").exists():
        from vector_room import bounds

        assert bounds(M, w) == json.loads((d / "vector_room.json").read_text())
    if (d / "matrix_upper.json").exists():
        from fractions import Fraction
        from fixed_matrix import bound as fixed_matrix_bound

        assert (
            Fraction(w["classical_upper_numerator"], w["classical_upper_denominator"])
            == w["attained"]
        )
        full = fixed_matrix_bound(
            M, json.loads((d / "matrix_upper.json").read_text()), w["attained"]
        )
        assert ratio <= full
        print(
            "Checked the vector upper for the fixed matrix in arbitrary dimension.", flush=True
        )
    if (d / "model_dual.json").exists():
        from band_certificate import second_endpoint
        from model_dual import bound

        _, _, perms = second_endpoint(ROOT, base, first, I, sym)
        up, _ = bound(w, center, perms, json.loads((d / "model_dual.json").read_text()))
        assert up >= ratio
        dc = json.loads((d / "model_dual.json").read_text())
        if "dictionary_budget" in w:
            allowed = {json.dumps(x, sort_keys=True) for x in dc["dictionary_arrays"]}
            assert all(
                json.dumps(x["atom"], sort_keys=True) in allowed
                for x in json.loads((d / "extra_games.json").read_text())
            )
        if "listed_upper_numerator" in dc:
            allowed = set(tuple(g) for g in dc["chsh_dictionary"])
            for term in json.loads((d / "games.json").read_text()):
                aa, bb, cc, dd = term["entries"]
                g = (aa[0], bb[0], aa[1], cc[1], aa[2], cc[2])
                assert g in allowed and bb == [g[1], g[2], g[4]] and dd == [g[1], g[3], -g[5]]

            restricted, _ = bound(w, center, perms, dc, False)
            assert ratio <= restricted <= up
        print("Checked the fixed-vector upper for the matrix optimization.", flush=True)
    if opt.vectors_only:
        print("Verified witness arithmetic against the archived reference list.", flush=True)
        return
    with tempfile.TemporaryDirectory(dir=opt.scratch, prefix="order-three-") as name:
        tmp = Path(name)
        flags = ["-O3", "-std=c++17", "-fopenmp"]
        if not opt.portable:
            flags += ["-march=native"]
        for exe in (
            "enumerate",
            "conditional_block",
            "check_margin",
            "shallow_fast",
            "score_band",
        ):
            subprocess.run(
                [opt.compiler, *flags, str(ROOT / (exe + ".cpp")), "-o", str(tmp / exe)],
                check=True,
            )
        from test_band import run

        run(tmp, tmp / "check_margin", tmp / "shallow_fast", tmp / "conditional_block")
        C = 320975646
        B = w["reference_margin"]
        cv = json.loads((ROOT / "cover.json").read_text())
        mul = cv["multiplier"]
        upper = caps(base, center, I, sym, cv, tmp / "conditional_block", tmp, opt.threads)
        L = {
            r: max(0, (v - C + mul - 2) // (mul - 1)) + (B + mul - 2) // (mul - 1)
            for r, v in upper.items()
        }
        largest = max(L.values())
        threshold = C - B - largest
        assert largest == 6488158 and threshold == 314271488
        cf = tmp / "caps.txt"
        cf.write_text("".join(f"{r} {v}\n" for r, v in L.items()))
        print(
            "Checked all",
            len(L),
            "conditional bounds. Enumerating the original signings.",
            flush=True,
        )
        near = tmp / "near.bin"
        th = str(opt.threads)
        subprocess.run(
            [
                str(tmp / "enumerate"),
                str(ROOT / "base.txt"),
                str(ROOT / "base.txt"),
                str(ROOT / "tails.txt"),
                str(threshold),
                th,
                "12",
                "--symmetry",
                str(ROOT / "symmetry.txt"),
                "--enumerate-above",
                "--packed-near",
                str(near),
            ],
            check=True,
        )
        with near.open("rb") as f:
            assert f.read(8) == b"K3SIG001" and struct.unpack("<IIIQ", f.read(20)) == (
                len(base),
                len(base[0]),
                threshold,
                7832114,
            )
        active = tmp / "second.bin"
        subprocess.run(
            [
                str(tmp / "check_margin"),
                str(ROOT / "base.txt"),
                str(d / "endpoint.txt"),
                str(ROOT / "split_rows.txt"),
                str(ROOT / "symmetry.txt"),
                str(near),
                str(threshold),
                str(C),
                th,
                str(largest),
                str(cf),
                str(active),
                str(B),
            ],
            check=True,
        )
        data = set(struct.iter_unpack("<6I", active.read_bytes()))
        stored = set(struct.iter_unpack("<6I", saved.read_bytes()))
        assert len(stored) == w["records"] and data == stored
        check_scores(ROOT, w, saved, tmp / "score_band")
        print("Verified K_G(3) >", w["strict_lower_bound"], flush=True)


if __name__ == "__main__":
    main()

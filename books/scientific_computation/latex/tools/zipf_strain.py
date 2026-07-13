#!/usr/bin/env python3
"""Prose-only, truncated-Zipf gauge for Volume 4.

This is a lexical diagnostic, never an honesty or correctness check.  Mathematics,
code, citations, and LaTeX control syntax are excluded from the fitted channel.
The fit population is the target's own 1..1000 most frequent prose word types;
"top 1000" does not mean a whitelist of common English words.
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import math
import random
import re
import statistics
import unicodedata
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
LATEX = HERE.parent
ROOT = HERE.parents[3]
DEFAULT_TARGET = LATEX / "chapters"
DEFAULT_BASELINE = (
    ROOT / "books/expository_monograph/vol1/chapters",
    ROOT / "books/experimentation/vol2/chapters",
    ROOT / "books/the_compiler/vol3/chapters",
)
TOP_RANKS = 1000
LOCAL_RANKS = 300
BOOTSTRAPS = 50
WINDOW = 400
STEP = 50
GAUSS_SIGMA = 2.5

MATH_ENVS = (
    "equation", "align", "alignat", "gather", "multline", "displaymath",
    "math", "array", "cases", "matrix", "pmatrix", "bmatrix", "vmatrix",
    "Vmatrix", "split", "aligned", "alignedat", "gathered",
)
CODE_ENVS = ("verbatim", "verbatimtab", "lstlisting", "minted", "alltt")

STOPWORDS = set(
    "a an and are as at be been being but by can could did do does for from had "
    "has have he her hers him his how i if in into is it its itself may me might "
    "more most must my no nor not of on one only or our ours shall she should so "
    "some such than that the their theirs them themselves then there these they "
    "this those through to too under up us very was we were what when where which "
    "while who whom why will with would you your yours".split()
)


@dataclass
class Fit:
    tokens: int
    types: int
    fitted_ranks: int
    exponent: float
    hapax: int


def files_in(paths: Sequence[Path]) -> list[Path]:
    out: list[Path] = []
    for path in paths:
        out.extend(Path(p) for p in sorted(glob.glob(str(path / "*.tex"))))
    return out


def strip_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", " ", text)


def prose_channel(text: str) -> str:
    """Remove non-prose channels while retaining arguments of prose commands."""
    text = strip_comments(text)
    envs = "|".join(map(re.escape, MATH_ENVS + CODE_ENVS))
    text = re.sub(
        rf"\\begin\{{({envs})\}}.*?\\end\{{\1\}}", " ", text,
        flags=re.DOTALL,
    )
    text = re.sub(r"\\verb(.).*?\1", " ", text, flags=re.DOTALL)
    text = re.sub(r"(?<!\\)\$\$.*?(?<!\\)\$\$", " ", text, flags=re.DOTALL)
    text = re.sub(r"\\\[.*?\\\]", " ", text, flags=re.DOTALL)
    text = re.sub(r"\\\(.*?\\\)", " ", text, flags=re.DOTALL)
    text = re.sub(r"(?<!\\)\$(?:\\.|[^$])*?(?<!\\)\$", " ", text, flags=re.DOTALL)
    # Metadata/cross-reference arguments are not manuscript prose.
    text = re.sub(
        r"\\(?:cite|parencite|textcite|autocite|ref|eqref|pageref|label|index|url)"
        r"\*?(?:\[[^]]*\])*\{[^{}]*\}",
        " ", text,
    )
    text = re.sub(r"\\href\{[^{}]*\}\{([^{}]*)\}", r" \1 ", text)
    # Remove command names/options, but retain ordinary braced prose arguments
    # (e.g. \emph{word} -> word).
    text = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])*", " ", text)
    text = re.sub(r"\\.", " ", text)
    return re.sub(r"[{}&#_^~]", " ", text)


def tokenize(text: str) -> list[str]:
    text = unicodedata.normalize("NFKC", prose_channel(text)).lower()
    text = text.replace("’", "'").replace("–", "-").replace("—", "-")
    return re.findall(r"[a-z]+(?:['-][a-z]+)*", text)


def load(paths: Sequence[Path]) -> tuple[list[str], list[tuple[str, str]]]:
    tokens: list[str] = []
    stream: list[tuple[str, str]] = []
    for path in files_in(paths):
        chapter = path.name
        chapter_tokens = tokenize(path.read_text(encoding="utf-8", errors="ignore"))
        tokens.extend(chapter_tokens)
        stream.extend((token, chapter) for token in chapter_tokens)
    return tokens, stream


def fit(tokens: Sequence[str], top: int = TOP_RANKS) -> tuple[Fit, Counter[str], list[tuple[str, int]]]:
    counts = Counter(tokens)
    ranked = counts.most_common()
    head = ranked[:top]
    if len(head) < 3:
        exponent = float("nan")
    else:
        xs = [math.log(rank) for rank in range(1, len(head) + 1)]
        ys = [math.log(freq) for _, freq in head]
        mx, my = statistics.fmean(xs), statistics.fmean(ys)
        denominator = sum((x - mx) ** 2 for x in xs)
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / denominator
        exponent = -slope
    return Fit(len(tokens), len(counts), len(head), exponent,
               sum(1 for freq in counts.values() if freq == 1)), counts, ranked


def mean_sd(values: Sequence[float]) -> tuple[float, float]:
    mean = statistics.fmean(values)
    sd = math.sqrt(statistics.fmean((value - mean) ** 2 for value in values))
    return mean, sd


def matched_baseline(base: Sequence[str], n: int, *, top: int, seeds: int,
                     seed_offset: int) -> tuple[float, float]:
    if n >= len(base):
        return fit(base, top)[0].exponent, 0.0
    values = []
    for seed in range(seeds):
        sample = random.Random(seed_offset + seed).sample(list(base), n)
        values.append(fit(sample, top)[0].exponent)
    return mean_sd(values)


def half_length(tokens: Sequence[str], *, seeds: int) -> tuple[float, float]:
    n = len(tokens) // 2
    values = []
    for seed in range(seeds):
        sample = random.Random(1000 + seed).sample(list(tokens), n)
        values.append(fit(sample)[0].exponent)
    return mean_sd(values)


def math_fraction(paths: Sequence[Path]) -> tuple[float, int, int]:
    total = prose = 0
    for path in files_in(paths):
        raw = path.read_text(encoding="utf-8", errors="ignore")
        total += len(raw)
        prose += len(prose_channel(raw))
    nonprose = max(0, total - prose)
    return (nonprose / total if total else 0.0, nonprose, prose)


def source_hash(paths: Sequence[Path]) -> str:
    digest = hashlib.sha256()
    for path in files_in(paths):
        digest.update(path.name.encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()


def gaussian(values: Sequence[float], sigma: float) -> list[float]:
    radius = max(1, int(3 * sigma))
    kernel = [math.exp(-(i * i) / (2 * sigma * sigma))
              for i in range(-radius, radius + 1)]
    smoothed = []
    for pos in range(len(values)):
        weighted = norm = 0.0
        for offset, weight in zip(range(-radius, radius + 1), kernel):
            idx = pos + offset
            if 0 <= idx < len(values):
                weighted += values[idx] * weight
                norm += weight
        smoothed.append(weighted / norm)
    return smoothed


def percentile(values: Sequence[float], q: float) -> float:
    if not values:
        return float("nan")
    ordered = sorted(values)
    index = (len(ordered) - 1) * q
    lo, hi = math.floor(index), math.ceil(index)
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - index) + ordered[hi] * (index - lo)


def seam_map(stream: Sequence[tuple[str, str]], counts: Counter[str],
             base_counts: Counter[str]) -> dict:
    content_head = [word for word, _ in counts.most_common()
                    if word not in STOPWORDS][:50]
    head = set(content_head)
    technical = set(counts) - set(base_counts)
    windows = []
    for start in range(0, max(0, len(stream) - WINDOW + 1), STEP):
        sample = stream[start:start + WINDOW]
        words = [word for word, _ in sample]
        chapter = sample[WINDOW // 2][1]
        windows.append({
            "token": start + WINDOW // 2,
            "chapter": chapter,
            "head_density": sum(word in head for word in words) / WINDOW,
            "type_ratio": len(set(words)) / WINDOW,
            "technical_density": sum(word in technical for word in words) / WINDOW,
        })
    features = ("head_density", "type_ratio", "technical_density")
    gradients: list[float] = [0.0] * len(windows)
    for feature in features:
        smooth = gaussian([row[feature] for row in windows], GAUSS_SIGMA)
        raw = [0.0] + [abs(smooth[i + 1] - smooth[i - 1]) / 2
                       for i in range(1, len(smooth) - 1)] + [0.0]
        scale = percentile(raw, 0.95) or 1.0
        for i, value in enumerate(raw):
            gradients[i] += value / scale
    gradients = [value / len(features) for value in gradients]
    within = [gradients[i] for i in range(1, len(windows) - 1)
              if windows[i - 1]["chapter"] == windows[i]["chapter"] == windows[i + 1]["chapter"]]
    threshold = percentile(within, 0.95)
    peaks = []
    for i in range(1, len(windows) - 1):
        same = windows[i - 1]["chapter"] == windows[i]["chapter"] == windows[i + 1]["chapter"]
        if same and gradients[i] >= gradients[i - 1] and gradients[i] > gradients[i + 1]:
            peaks.append({"score": gradients[i], "token": windows[i]["token"],
                          "chapter": windows[i]["chapter"],
                          "strong": gradients[i] >= threshold})
    peaks.sort(key=lambda row: row["score"], reverse=True)
    return {"window": WINDOW, "step": STEP, "gaussian_sigma": GAUSS_SIGMA,
            "empirical_p95": threshold, "top_content_words": content_head,
            "peaks": peaks[:8]}


def chapter_report(target: Sequence[Path], base_tokens: Sequence[str], seeds: int) -> list[dict]:
    rows = []
    for path in files_in(target):
        tokens = tokenize(path.read_text(encoding="utf-8", errors="ignore"))
        local, counts, ranked = fit(tokens, LOCAL_RANKS)
        base_mean, base_sd = matched_baseline(
            base_tokens, len(tokens), top=LOCAL_RANKS, seeds=seeds, seed_offset=4000)
        content = [(word, freq) for word, freq in ranked if word not in STOPWORDS][:5]
        rows.append({"chapter": path.name, "tokens": local.tokens, "types": local.types,
                     "fitted_ranks": local.fitted_ranks, "exponent": local.exponent,
                     "baseline": base_mean, "baseline_sd": base_sd,
                     "strain": local.exponent - base_mean, "content_head": content})
    return rows


def analyze(target: Sequence[Path], baseline: Sequence[Path], seeds: int) -> dict:
    target_tokens, stream = load(target)
    base_tokens, _ = load(baseline)
    target_fit, target_counts, ranked = fit(target_tokens)
    _, base_counts, _ = fit(base_tokens)
    base_mean, base_sd = matched_baseline(
        base_tokens, len(target_tokens), top=TOP_RANKS, seeds=seeds, seed_offset=2000)
    half_mean, half_sd = half_length(target_tokens, seeds=seeds)
    drift = abs(target_fit.exponent - half_mean)
    nonprose_fraction, nonprose_chars, prose_chars = math_fraction(target)
    return {
        "schema": "vol4-prose-zipf-v1",
        "meaning_of_top_1000": "target-internal frequency ranks 1..1000, not an English whitelist",
        "target": [str(path) for path in target],
        "baseline": [str(path) for path in baseline],
        "source_sha256": source_hash(target),
        "settings": {"top_ranks": TOP_RANKS, "local_ranks": LOCAL_RANKS,
                     "bootstrap_seeds": seeds, "math_and_code_excluded": True},
        "target_fit": asdict(target_fit),
        "baseline_matched": {"exponent_mean": base_mean, "sd": base_sd,
                             "ci95": [base_mean - 1.96 * base_sd, base_mean + 1.96 * base_sd]},
        "strain": target_fit.exponent - base_mean,
        "length_convergence": {"half_mean": half_mean, "sigma": half_sd,
                               "drift": drift, "converged": drift < half_sd,
                               "temperature": drift / half_sd if half_sd else None},
        "channels": {"nonprose_fraction_of_source_chars": nonprose_fraction,
                     "nonprose_chars": nonprose_chars, "prose_channel_chars": prose_chars},
        "content_head": [(word, freq) for word, freq in ranked
                         if word not in STOPWORDS][:20],
        "chapters": chapter_report(target, base_tokens, seeds),
        "seams": seam_map(stream, target_counts, base_counts),
        "warning": "Lexical diagnostic only; never evidence of truth, grounding, or executable correspondence.",
    }


def markdown(report: dict) -> str:
    fit_row = report["target_fit"]
    baseline = report["baseline_matched"]
    convergence = report["length_convergence"]
    channels = report["channels"]
    lines = [
        "# Volume 4 prose-only Zipf baseline",
        "",
        f"Source SHA-256: `{report['source_sha256']}`",
        "",
        "> Lexical diagnostic only. It does not establish truth, grounding, provenance, or executable correspondence.",
        "",
        "## Whole manuscript",
        "",
        f"- Prose tokens: **{fit_row['tokens']:,}**; types: **{fit_row['types']:,}**; hapax: **{fit_row['hapax']:,}**.",
        f"- Truncated fit: ranks **1–{fit_row['fitted_ranks']}** of the manuscript's own prose vocabulary; `s = {fit_row['exponent']:.6f}`.",
        f"- Matched-length Volumes 1–3 baseline: `s0 = {baseline['exponent_mean']:.6f} ± {baseline['sd']:.6f}` (bootstrap SD).",
        f"- Strain: **{report['strain']:+.6f}**.",
        f"- Length test: drift `{convergence['drift']:.6f}` vs sigma `{convergence['sigma']:.6f}`; converged = **{str(convergence['converged']).lower()}**; `T = {convergence['temperature']:.3f}`.",
        f"- Excluded math/code/markup channel: **{100 * channels['nonprose_fraction_of_source_chars']:.1f}%** of source characters.",
        "",
        "A negative strain is a locator and trajectory measure, not an instruction to remove necessary technical vocabulary.",
        "",
        "## Content head",
        "",
        ", ".join(f"`{word}` {freq}" for word, freq in report["content_head"]),
        "",
        "## Chapter-local fits",
        "",
        "| Chapter | Tokens | Types | Local ranks | s | Matched s0 | Strain | Content head |",
        "|---|---:|---:|---:|---:|---:|---:|---|",
    ]
    for row in report["chapters"]:
        head = ", ".join(f"{word}:{freq}" for word, freq in row["content_head"])
        lines.append(
            f"| {row['chapter']} | {row['tokens']} | {row['types']} | {row['fitted_ranks']} | "
            f"{row['exponent']:.4f} | {row['baseline']:.4f} | {row['strain']:+.4f} | {head} |"
        )
    seams = report["seams"]
    lines += [
        "", "## Within-chapter seam candidates", "",
        f"Windows `{seams['window']}`, step `{seams['step']}`, Gaussian sigma `{seams['gaussian_sigma']}`; "
        f"strong means at or above the manuscript's empirical within-chapter p95 (`{seams['empirical_p95']:.4f}`).",
        "", "| Score | Chapter | Token | Strong |", "|---:|---|---:|:---:|",
    ]
    for row in seams["peaks"]:
        lines.append(f"| {row['score']:.4f} | {row['chapter']} | {row['token']} | {'yes' if row['strong'] else 'no'} |")
    lines += [
        "", "## Reproduction", "",
        "```sh", "python3 tools/zipf_strain.py --format markdown", "```", "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", nargs="?", type=Path, default=DEFAULT_TARGET)
    parser.add_argument("--baseline", type=Path, action="append",
                        help="baseline chapter directory; repeat for multiple volumes")
    parser.add_argument("--seeds", type=int, default=BOOTSTRAPS)
    parser.add_argument("--format", choices=("markdown", "json"), default="markdown")
    args = parser.parse_args()
    baselines = tuple(args.baseline) if args.baseline else DEFAULT_BASELINE
    report = analyze((args.target,), baselines, args.seeds)
    print(json.dumps(report, indent=2) if args.format == "json" else markdown(report))


if __name__ == "__main__":
    main()

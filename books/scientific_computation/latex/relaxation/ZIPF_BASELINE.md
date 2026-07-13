# Volume 4 prose-only Zipf baseline

Source SHA-256: `2b7d220decd7d3fa91c2b2b6964c9937c1ccd705cfafa3c4d5d3c93443a753e8`

Compiled PDF at baseline: **242 pages** (`scientific_computation.pdf`).

> Lexical diagnostic only. It does not establish truth, grounding, provenance, or executable correspondence.

## Whole manuscript

- Prose tokens: **40,011**; types: **3,474**; hapax: **1,268**.
- Truncated fit: ranks **1–1000** of the manuscript's own prose vocabulary; `s = 0.891057`.
- Matched-length Volumes 1–3 baseline: `s0 = 1.075592 ± 0.004057` (bootstrap SD, 50 deterministic samples).
- Strain: **-0.184535**.
- Length test: drift `0.000602` vs sigma `0.005770`; converged = **true**; `T = 0.104`.
- Excluded math/code/markup channel: **20.4%** of source characters.

A negative strain is a locator and trajectory measure, not an instruction to remove necessary technical vocabulary.

## Content head

`declared` 230, `exact` 227, `certificate` 203, `finite` 192, `physical` 175, `equality` 167, `model` 164, `computation` 153, `comparison` 143, `order` 137, `budgets` 135, `stop` 134, `worked` 133, `uncertainty` 132, `records` 128, `calibration` 128, `example` 125, `stops` 124, `arithmetic` 122, `report` 121

## Chapter-local fits

| Chapter | Tokens | Types | Local ranks | s | Matched s0 | Strain | Content head |
|---|---:|---:|---:|---:|---:|---:|---|
| 1.tex | 3625 | 938 | 300 | 0.7431 | 0.9190 | -0.1759 | finite:36, two:20, declared:20, comparison:19, projection:19 |
| 10.tex | 2329 | 734 | 300 | 0.6957 | 0.9080 | -0.2123 | exact:20, quotient:20, certificate:15, model:15, remainder:14 |
| 11.tex | 2648 | 802 | 300 | 0.6794 | 0.8810 | -0.2016 | counter:28, configuration:18, exact:17, declared:16, target:15 |
| 12.tex | 2796 | 863 | 300 | 0.7080 | 0.8779 | -0.1699 | arithmetic:29, exact:27, boundary:27, declared:23, model:22 |
| 13.tex | 2573 | 751 | 300 | 0.6980 | 0.8864 | -0.1884 | exact:30, report:17, certificate:17, rational:16, quadrature:16 |
| 14.tex | 2498 | 680 | 300 | 0.6986 | 0.8929 | -0.1943 | equality:36, proposition:23, exact:22, declared:18, two:17 |
| 15.tex | 2876 | 804 | 300 | 0.6825 | 0.8821 | -0.1996 | physical:20, exact:20, dependency:19, declared:18, report:17 |
| 2.tex | 2497 | 708 | 300 | 0.7622 | 0.8929 | -0.1307 | finite:32, update:31, declared:19, example:17, question:16 |
| 3.tex | 2297 | 626 | 300 | 0.7444 | 0.9097 | -0.1653 | question:20, history:20, example:19, error:19, worked:18 |
| 4.tex | 2784 | 797 | 300 | 0.7322 | 0.8777 | -0.1455 | finite:25, requirement:20, direct:18, witness:17, forward:16 |
| 5.tex | 2726 | 800 | 300 | 0.7550 | 0.8770 | -0.1219 | exact:26, bracket:24, report:23, certificate:18, crossing:17 |
| 6.tex | 2871 | 846 | 300 | 0.7006 | 0.8817 | -0.1811 | stop:30, width:20, route:17, declared:17, grid:16 |
| 7.tex | 2690 | 816 | 300 | 0.6940 | 0.8783 | -0.1843 | equality:24, model:20, certificate:18, calibration:17, declared:16 |
| 8.tex | 2298 | 670 | 300 | 0.7650 | 0.9097 | -0.1447 | state:27, collision:24, transition:22, map:20, cycle:20 |
| 9.tex | 2503 | 761 | 300 | 0.7071 | 0.8921 | -0.1850 | order:32, physical:20, phase:20, uncertainty:18, permutation:17 |

## Within-chapter seam candidates

Windows `400`, step `50`, Gaussian sigma `2.5`; strong means at or above the manuscript's empirical within-chapter p95 (`0.7108`). Scores combine normalized gradients in content-head density, type ratio, and technical-term density.

| Score | Chapter | Token | Strong |
|---:|---|---:|:---:|
| 0.8750 | 9.tex | 38250 | yes |
| 0.8690 | 13.tex | 13550 | yes |
| 0.8185 | 11.tex | 8250 | yes |
| 0.8027 | 9.tex | 38750 | yes |
| 0.7966 | 9.tex | 39600 | yes |
| 0.7855 | 6.tex | 29700 | yes |
| 0.7824 | 12.tex | 8700 | yes |
| 0.7621 | 14.tex | 14350 | yes |

## Reproduction

From `books/scientific_computation/latex`:

```sh
python3 tools/zipf_strain.py --format markdown
python3 tools/zipf_strain.py --format json
```

The stored report adds the compiled page count; all lexical values above are emitted by the tool.

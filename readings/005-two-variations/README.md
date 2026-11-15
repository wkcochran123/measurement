# 005 — Two first variations, and the convective term

The first variation has two representations: time-like (along the clock at a place: the local rate) and space-like
(across places at one time: the difference between levels, summed into a potential). Navier-Stokes joins them in the
material derivative, the time-like variation plus the convective term u . grad u. Receipts in Episode 12:
`a_boost_keeps_the_kind`, `time_like_stays_time_like`, `space_like_stays_space_like`,
`one_variation_two_representations`, `the_convective_term` (2 u d = (u+d)^2 - u^2 - d^2).

- `gen_steps.py K`, `probe_steps.lean`: step k decides k+1 cells, each term new, `STEP k cells raw blank ns`.
- `run_steps.sh <CARD_2> <probe> <runs>`, `analyze_steps.py <M2> <Ultra>`; `SEALED_PREDICTION.txt` written first.

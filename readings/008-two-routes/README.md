# 008 — Two routes to one number

The ladder read down (Episode 12, `THE LADDER, READ DOWN`) says the two versions agree at every rung, and that what
separates them is conserved and measurable. The device has two routes to its number that share no step: the crank
(Newton: it uses the derivative, a limit) and the halving (bisection: it uses only the sign of the residual). That they
meet is already a receipt: `the_reading_with_its_receipt` (the crank's point lies in the halving's bracket, under one
place), minted as `THE_CH_VERSION_IS_THE_NON_CH_VERSION` with `the_two_versions_click`.

This experiment reads what each route costs. Episode 12 already meters the halving (`theHalvingBeats`); it does not meter
the crank. Here both are metered turn by turn in one process.

- `probe_routes.lean`: the halving first. `probe_routes_crank_first.lean`: the crank first.
  Output: `BLANK hb ns`, `HALVING i hb ns`, `CRANK i hb ns`, `MEET bracket point`.
- `run_routes.sh <CARD_2> <probe> <runs>`: one fresh process per run.
- `analyze_routes.py <halving-first output> <crank-first output>`: reports each sealed item.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below and this file is what the setup commit carries.

Observable: heartbeats (the elaborator's count of its own allocations) and wall time, per turn.
Boundary: `withHeartbeats` around one call of `halve` or of `the_truth_inferred_by_the_device`.
Baseline: `BLANK`, the meter around nothing.
What tells the accounts apart: whether the two totals agree within one per cent.

The probes run compiled definitions in the elaborator, as the build's own `frechet_walk` does. Nothing is unfolded in the
kernel.

Source: the setup commit that adds this folder. Status: sealed, not run.

## The seal

```
Experiment 008, two routes to one number. Sealed Mon Nov 16 10:12:27 EST 2026, before any run of these probes
was read. (Each probe was afterwards executed once to check that it compiles, with its output discarded unread.)

Workload: in one fresh process, the halving (bisection: the sign of the residual only) and the crank (Newton: the
derivative), each run one turn per cell of the strip (episode8_description.length turns), every turn under
withHeartbeats with wall time. Two probes: the halving first, and the crank first. Five runs of each.
H = total heartbeats of the halving, C = total heartbeats of the crank, in the first run of the halving-first probe.

The author's statement, 16 November 2026: "BULLSHIT IS STRICTLY CONSERVED because OF LOAD and SCALE we can measure the
MAGNITUDE OF BULLSHIT to get the VALUE OF the EXECUTED COMPILED CODE".

 (a) The heartbeat count at every turn of both routes is identical across runs and does not depend on which route
     runs first.
 (b) Both routes meet the build's own: the halving ends on theBracket and the crank on theNewtonPoint (MEET true true).

Two accounts of the totals. They exclude each other.
 (c) Account A, conservation read strictly: |H - C| <= 1% of the larger. The author's sentence is the author's; reading
     it as equality of these two totals is Claude's, proposed, and the author may replace it before the run.
 (d3) Account B, structure (Claude's): |H - C| > 1% of the larger. No direction is sealed.

Also sealed, Claude's, from the structure of the loops:
 (d1) A heartbeat counts allocations, not the size of the numbers, so the halving's heartbeats per turn are flat: after
      the first three turns, (max - min) <= 10% of the mean.
 (d2) Wall time does see the size: the mean wall time per halving over the last third of the turns exceeds the mean over
      turns 3 to the end of the first third.

Would refute: (a) any turn differing between runs or between orders; (b) a MEET other than true true; (c) a difference
above 1%; (d3) a difference of 1% or less; (d1) a spread above 10%; (d2) the last third not slower than the first.

What no outcome establishes: that a heartbeat is a unit of physical cost, or that either route is the continuous one.
Naming the crank the version that takes a limit and the halving the version that does not is the reading under test's
premise, not its result.
```

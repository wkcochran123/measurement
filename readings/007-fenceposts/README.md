# 007 — The five-block fencepost

The author reads 004's mixed fit of relative time as a five-block fencepost: the 36 levels are seven panels of five
with one post over (36 = 7 x 5 + 1, the 35 lifts and the post). If relative time is read panel by panel, its shape
breaks at the posts. `analyze_posts.py` fits ln R by a continuous piecewise-linear spline with six interior knots on the
post grid and on the grid shifted by one to four levels, and compares the residuals. Probe and runner copied from 004.

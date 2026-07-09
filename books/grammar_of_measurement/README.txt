Grammar of Measurement
======================

This workspace is for the recursive TeX draft pass requested on 2026-07-08.

The manuscript rule is strict:

- write the book in TeX;
- keep manuscript files 7-bit ASCII;
- describe how the grammar enforces the plot, not how an implementation does it;
- do not name the formal system or the presence of code in the manuscript;
- use experiment examples as illustrations of the grammar, not as the spine.

Recursive workflow:

1. The top-level scheduler handles one chapter at a time.
2. A chapter manager owns the chapter directory and decomposes one plot point.
3. A section manager owns one beat or cluster of beats and decomposes it.
4. Writers draft small fragments.
5. Managers merge fragments into sections, sections into chapters, and chapters into the book.

Progress is visible under work/status.txt and work/chapters/*/status.txt.


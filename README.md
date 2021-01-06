# Isabelle/HOL solutions to math contest problems

This repository contains various [Isabelle/HOL] formal proofs. This is mostly solutions
to interesting math olympiad problems, but some higher math exercises have found their way
here, too.

Apart from that, I keep some [notes] on the mathematical library of Isabelle. This includes
situations where the structure and interaction of objects 

I encourage you to explore.

[notes]: https://github.com/NieDzejkob/isabelle-math-contests/blob/master/NOTES.md
[Isabelle/HOL]: https://isabelle.in.tum.de/

<!-- BEGIN DYNAMIC CONTENT -->

## Whoops

You probably want to see [the other branch][redirect]. See the section to below if
you're curious why this is necessary.

<!-- TODO: add a README anchor to this link -->
[redirect]: https://github.com/NieDzejkob/isabelle-math-contests/tree/built-pdfs

<!-- END DYNAMIC CONTENT -->

## Structure of this repository

Raw Isabelle `.thy` files are hard to look at. As can be expected for math,
lots of non-ASCII characters are involved. Apart from font issues, Isabelle actually
predates Unicode, so the text files are actually encoded with LaTeX-ish escape sequences.

This motivates a sophisticated CI setup (the three words you don't ever want to see next
to each other). The `master` branch of the repository keeps the sources, while GitHub
Actions render PDFs and push them onto the `built-pdfs` branch.

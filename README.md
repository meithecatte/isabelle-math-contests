# Isabelle/HOL solutions to math contest problems

This repository contains various [Isabelle/HOL] formal proofs. This is mostly solutions
to interesting math olympiad problems, but some higher math exercises have found their way
here, too.

Apart from that, I keep some [notes] on the mathematical library of Isabelle. This includes
situations where the structure and interaction of objects 

I encourage you to explore.

[notes]: https://github.com/NieDzejkob/isabelle-math-contests/blob/master/NOTES.md
[Isabelle/HOL]: https://isabelle.in.tum.de/

# Problems by origin

- <details>
  <summary>British Math Olympiad Round 1 [<i>1 problems</i>]</summary>
  
  - 2015
    - [Problem 2](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/BMO1/2015/BMO1-2015-Problem_2.pdf) (number theory)
    
  
  </details>
- <details>
  <summary>Polish Math Olympiad [<i>9 problems</i>]</summary>
  
  - 1969
    - <details>
      <summary>Round 1 [<i>7 problems</i>]</summary>
      
      - [Problem 1](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Problem_1.pdf) (number theory, diophantine equation)
      - [Problem 2](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Problem_2.pdf) (calculus)
      - [Problem 5](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Problem_5.pdf) (inequality)
      - [Warmup Problem A](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Warmup_Problem_A.pdf) (number theory, congruences)
      - [Warmup Problem B](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Warmup_Problem_B.pdf) (inequality, multiple solutions, calculus)
      - [Warmup Problem C](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Warmup_Problem_C.pdf) (equation)
      - [Warmup Problem D](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/1969/Round_1/Polish_MO-1969-Round_1-Warmup_Problem_D.pdf) (metric space, geometry)
      
      </details>
    
  - 2020
    - Round 1
      - [Problem 1](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/2020/Round_1/Polish_MO-2020-Round_1-Problem_1.pdf) (inequality)
      - [Problem 3](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Polish_MO/2020/Round_1/Polish_MO-2020-Round_1-Problem_3.pdf) (number theory)
      
    
  
  </details>
- <details>
  <summary>An Infinitely Large Napkin [<i>2 problems</i>]</summary>
  
  - [Problem 1A](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Napkin/Napkin-Problem_1A.pdf) (group theory)
  - [Problem 1B](https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/Napkin/Napkin-Problem_1B.pdf) (group theory)
  
  </details>


## Structure of this repository

Raw Isabelle `.thy` files are hard to look at. As can be expected for math,
lots of non-ASCII characters are involved. Apart from font issues, Isabelle actually
predates Unicode, so the text files are actually encoded with LaTeX-ish escape sequences.

This motivates a sophisticated CI setup (the three words you don't ever want to see next
to each other). The `master` branch of the repository keeps the sources, while GitHub
Actions render PDFs and push them onto the `built-pdfs` branch.

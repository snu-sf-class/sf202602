# Software Formal Verification, SNU M1522.007300, 2026 Fall

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
    + Email address: gil.hur@sf.snu.ac.kr
    + Office: 302-426
- TA: [Sunho Park](http://sf.snu.ac.kr/sunho.park)
    + Email address: sf@sf.snu.ac.kr
        * When sending TA an email,
            * The subject (제목) must start with [SF]
            * Your name and student ID must be included in the body (본문)
    + Office: 302-315-1
- Class material: http://www.cis.upenn.edu/~bcpierce/sf/current/index.html
- Please use email to ask questions (Do not use GitHub Issues)

## Grading(tentative)

- Attendance: 5%
- Midterm: 45%
- Final: 50%

## Announcements

- Oct. 6:
    + Assignments 1, 2, 3 are uploaded.
    + Midterm exam will be held in Oct. 31th. Please check instructions through [this page](exam/midterm/README.md).
- Oct. 27:
    + Details about the midterm exam have been announced in the [README](exam/midterm/README.md).
- Nov. 22:
    + Midterm scores are released at etl website.
    + Please claim until Nov. 27th via email.
    + Statistics: (Q1, Q2, Q3, mean) = (50, 65, 80, 63.7)
        * Also see the [histogram](exam/midterm/result.png)

## Assignments (optional)

- Download skeleton code and replace `FILL_IN_HERE` with your code in P**.v.
- Each assignment have forbidden keyword in forbidden.txt. Try not to use those keywords.
- We will not be grading assignments - feel free to complete them and test your understanding about the materials dealt in the classes.
- Consult to the TA if you have any questions.

## Rocq (Coq)

- Install Rocq [9.0.0](https://coq.inria.fr).
    + Using an installer (Windows, MacOS)
        * Download [Binaries](https://coq.inria.fr/download) and install it.
        * Using Coq in Windows could have unexpected, unsupported problem. TA cannot help you in this case.

    + Using OPAM (Linux / MacOS) (recommended)
        * OPAM is OCaml package manager, and you can use it to install Coq in Linux.
        * See [https://coq.inria.fr/opam-using.html](https://coq.inria.fr/opam-using.html).

    + Using brew (MacOS)
        * Run `brew install coq`.
        * Note this wouldn't install CoqIDE.

- Install IDE for Coq.
    + CoqIDE: installed by default.
    + VS Code: [VSCoq](https://github.com/coq-community/vscoq/tree/vscoq1). Follow the setup instructions.
        * VsCoq v2.x is new and shows unstableness. If you have trouble using VsCoq v2, downgrade to VsCoq Legacy (v0.3.9).
        * Basic command (based on vscoq github page)
            * ```alt + down``` : interpret next step
            * ```alt + up``` : return to previous step
            * ```alt + right``` : interpret to right before cursor
            * ```alt + end``` : interpret until end of file
            * ```alt + home``` : reset
            * more commands : ```F1``` & type ```Coq:```
                * example : ```Coq: Prompt Check```
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.
        * If it shows `Searching for program No such file or directory coqtop` error, please add `(custom-set-variables '(coq-prog-name "PATH/TO/coqtop"))` to `.emacs` file.
        * In case of MacOS, coqtop is at `/Applications/CoqIDE_8.9.1.app/Contents/Resources/bin/`.

- Tips for those using Windows
    + Using [WSL](https://learn.microsoft.com/ko-kr/windows/wsl/install) allows you work on linux.
    + In WSL, [WSL extension of VS Code](https://learn.microsoft.com/ko-kr/windows/wsl/tutorials/wsl-vscode) is recommended.

- It is likely that you will use your own laptop in mid-term and final exam. If you do not have a laptop or cannot install Coq on it, please let the TA know.

## CRIS

First, set up the git submodules for CRIS and CRIS examples by:

```sh
git submodule update --init --recursive
```

Install OPAM, then run:

```sh
opam switch create . --no-install # Optional if you want to set up the local development environment. Omitting it will install globally.
./CRIS-examples/CRIS/configure
cd CRIS-examples
make # `make -j`, `make -j8`, ... are also possible for parallel compilation.
```

This will automatically install Rocq 9.0.0 as well as necessary dependencies for CRIS.

If you install it with `opam switch create . --no-install`, then you'd probably need to:
- run `eval $(opam env)$` on your terminal to put the Rocq compiler on the $PATH
- add some settings to your IDE to properly detect the Rocq compiler

## Tactics

- You can look up manuals about [Basic tactics](https://coq.inria.fr/doc/V8.18.0/refman/proofs/writing-proofs/index.html), [Automatic solver](https://coq.inria.fr/refman/proofs/automatic-tactics/index.html), and [Ltac](https://coq.inria.fr/refman/proof-engine/ltac.html) for more information about proof techniques.

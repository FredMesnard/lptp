# LPTP - A Logic Program Theorem Prover

## Requirements:

- LPTP is implemented in Prolog. 
- LPTP runs under SICStus Prolog, GNU Prolog, SWI Prolog, Quintus Prolog, ECLiPSe, or CProlog. 
- The user interface of LPTP requires GNU Emacs or XEmacs.
- Proofs are typesetted with TeX.
- HTML files are created with Perl.


## How to install the LPTP - system?

### (0) Unpack the tar file with the command:

        `gunzip -c lptp-1.06.tar.gz | tar xf -`

A directory `lptp` is created with the following subdirectories:

```
        bin             (empty)
        doc             (user manual)
        etc             (Emacs mode, Perl scripts)
        examples        (examples)
        lib             (the library of LPTP)
        src             (the Prolog sources of LPTP)
        test            (test files)
        tex             (TeX macros)
        tmp             (empty, for temporary files)
```

### (1) Creating the file `system.pl` in the `lptp/src` directory:

- Goto the `lptp/src/prolog` directory.

- Choose the file appropriate for your Prolog system.

- Rename and copy the file into `lptp/src/system.pl`.

    Example: 

    `cp lptp/src/prolog/sicstus.pl lptp/src/system.pl`

- Change the following line in `lptp/src/system.pl`:

    `io__lptp_home('/home/staerk/lptp').`

- Replace the Prolog atom '/home/staerk/lptp' with the full  pathname to your LPTP directory. LPTP must know where it is located in the file system.


### (2) A first (optional) test: 

- Goto the `lptp/src` directory.
    
- Start Prolog.

- Consult the file `init.pl` or the file `initg.pl`:

    `?- consult('init.pl').`

     or

    `?- consult('initg.pl').`

- If there are no error messages, try the following test files:

```prolog
        ?- consult('../test/io/test_io.pl').
        ?- consult('../test/boot/test.pl').
        ?- halt.
```
- Some tests are executed. There should be no error messages.

- Otherwise you have to edit the predicates in the file:

     `lptp/src/system.pl.`

### (3) Compiling the LPTP system:

- If you are using SICStus Prolog, execute the command:

     `make sicstus` in the `lptp/src` directory.

    This command compiles LPTP and creates the file `src/lptp.ql`.

- If you are using GNU Prolog, execute the command:

     `make gprolog` in the `lptp/src` directory.

     This command compiles LPTP and creates the file `src/lptp`.

- Otherwise, if you are not using SICStus Prolog, do (3a) and (3b).

(3a) Execute the command `make lptp` in the `lptp/src` directory.

This command concatenates all Prolog source files into one big file `lptp.pl`.

(3b) Compile the file `lptp.pl` with your Prolog system.

- Example (SICStus Prolog):

```prolog
    unix> sicstus
        ?- prolog_flag(compiling,_,fastcode). 
        ?- consult('op.pl').    % operator declarations
        ?- fcompile('lptp.pl'). % lptp.ql
        ?- halt.
```

- Example (SWI-Prolog):

```prolog
    unix> pl
        ?- qcompile('lptp.pl'). % lptp.qlf
        ?- halt.
```

- Example (GNU Prolog):

```prolog
    unix> gplc --global-size 16384 -o lptp lptp.pl
```

### (4) The real test:

- Goto the `lptp/src` directory.

- Start Prolog with the compiled file.

- Example (SICStus Prolog):

```prolog
    unix> sicstus
        ?- load(lptp).
        ?- consult('all.pl').
    ?- halt.
```

- Example (GNU Prolog):

```prolog
    unix> make allg
        unix> lptp < allg.pl
```

- About 45,000 lines of formal proofs are checked.
- There should be no error messages.
- There may, however, be some LPTP-warnings.

- If there are too many error messages, uncomment some of the  files in `all.pl` using the percent sign `%`.

- Note: When LPTP processes files, it creates `*.tex` and  `*.thm` files in a temporary directory (default: `lptp/tmp`).

    - You can change the tmp directory as follows:

```prolog
        ?- load(lptp).
        ?- set(tmp,'/tmp').
        ?- consult('all.pl').
```

    - When the tests are done, quit Prolog and go to the directory `lptp/tmp`. You should see there several `*.thm` and  `*.tex` files.

### (5) Typesetting proofs with TeX:

- Try to typeset one of the `*.tex` files in the `lptp/tmp` directory.

    Example:

```
        tex nat.tex
        xdvi nat.dvi
```

- Note: Some `*.tex` files require `*.aux` files. You have  to typeset the `*.tex` files in the right order. For example, you 
have to typeset the file `nat.tex` before you typeset the file `list.tex`.

- Note: To use hyperlinks in DVI files, uncomment the corresponding lines in `tex/proofmacros.tex`. You need a version of xdvi that supports hyperlinks.


### (6) Creating HTML files of the library:

- Edit the string `"/usr/local/bin/perl"` in the files `pr2html.perl` and `pl2html.perl` in the `lptp/etc` directory.

- Goto the `lptp/lib` directory.

- Execute the command `make html`. 

- This creates a new directory `html`.

- Try `<your_browser> html/index.html` and surf through the LPTP library (where `<your_browser>` is your favorite browser)


### (7) Finishing the installation: 

- Move the compiled file `lptp.ql`  (or `lptp`) into the `lptp/bin` directory.

- Remove all the temporary files in the `lptp/tmp` directory.

- Read `lptp/doc/user.ps`.


## How to install the Emacs mode for LPTP?

(The Emacs mode is described in an appendix of `lptp/doc/user.ps`.)


### (1) Setting up `lptp-mode.el`:


- Change the the values of the variable `prolog-program-name` and `lptp-start-string` in `etc/lptp-mode.el`.

    - Example (Sicstus Prolog):

```lisp
        (defvar prolog-program-name "/usr/local/bin/sicstus"
            "Program name for invoking an inferior Prolog process.")

        (defvar lptp-start-string "load('/home/staerk/lptp/bin/lptp').\n"
            "The Prolog command to load the LPTP system into Prolog.")
```

    - Example (GNU Prolog):

```lisp
        (defvar prolog-program-name "/home/staerk/lptp/bin/lptp"
            "Program name for invoking an inferior Prolog process.")

        (defvar lptp-start-string ""
            "The Prolog command to load the LPTP system into Prolog.")
```

### (2) Compiling `lptp-mode.el`:

- Start Emacs.
- Compile the file `lptp/etc/lptp-mode.el` with the command `M-x byte-compile-file`.
- You can ignore the warnings regarding `comint-mode`s in the compile log.


### (3) Editing `.emacs`:

- Include the following into your `.emacs` file:

```bash
        (autoload 'lptp-mode "/home/staerk/lptp/etc/lptp-mode" 
            "Major mode for editing formal proofs" t)
        (setq auto-mode-alist 
            (cons '("\\.pr$" . lptp-mode) auto-mode-alist))
        (transient-mark-mode 1)
````
    Note: You have to change the string `"/home/staerk/lptp/etc/lptp-mode"`.


### (4) Testing the Emacs mode:

- Start Emacs with the file `lptp/lib/list/list.pr`.

- Emacs should go into LPTP-mode.
    
- There should be a menu "LPTP" in the menu bar.

- Choose the item "Run LPTP" from the "LPTP" menu (equivalent: try the command `M-x run-lptp-other-frame`).

- A new frame should appear with a Prolog process running LPTP.
     
- You should see the Banner "LPTP, Version ..."

- Goto the `list.pr` buffer and choose "Send buffer" from the  "LPTP" menu. 

- In the `*lptp*` buffer you should see `"! LPTP-Message: list o.k."`.

- Goto the `list.pr` buffer. If you double click on a formula, then the whole formula should be highlighted. 


### (5) Colored proofs:

- Try `M-x font-lock-mode` in the `list.pr` buffer.

- The keywords should appear in a different font/color.

- If you want to change the colors, include the following into  your `.emacs` file:

```lisp
        (add-hook 'font-lock-mode-hook
          (lambda ()
            (set-face-foreground font-lock-keyword-face "RoyalBlue")
            (set-face-foreground font-lock-reference-face "ForestGreen")
            (set-face-foreground font-lock-comment-face "OrangeRed") ))
```

- If you want that `lptp-mode` uses `font-lock-mode` per default, include the following into your `.emacs` file:

```lisp
    (add-hook 'lptp-mode-hook 'turn-on-font-lock)
```

### (6) How to use Emacs tags tables to browse through the library?

- Execute the command `make tags` in the `lptp/lib` directory (this requires a newer version of `etags` that has REGEXPs).

- This command creates a tags table `lptp/lib/TAGS`.

- Goto the `list.pr` buffer. 

- Put the cursor on a reference, for example on `plus:zero` in `by corollary(plus:zero)`, then type `M-.' (escape-dot)`.

- When you are asked for a tags table, choose `lptp/lib/TAGS`.

- Type `C-h C-f find-tag` to learn more about tags tables.


## For more information contact: 

Robert F. Staerk, staerk@inf.ethz.ch


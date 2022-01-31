;;; lptp-mode.el -- major mode for editing formal proofs with LPTP.

;;   Author: Robert Staerk <staerk@saul.cis.upenn.edu> 
;;  Created: Wed Feb 28 14:27:23 1996 
;;  Updated: Wed Jul 21 14:03:35 1999
;; Keywords: lptp, prolog

;;; Commentary:

;; Parts of this major mode are based on standard GNU Emacs prolog.el
;; written by Masanobu UMEDA <umerin@flab.flab.fujitsu.junet>.
;;
;; This file is not part of GNU Emacs.
;;
;; What does LPTP mode?
;;
;; - It creates the menu "LPTP".
;; - It uses comint-mode for the interaction with an inferior
;;   Prolog process.
;; - It has an indendation function for formal proofs.
;; - It has edit functions to select formulas and proof steps.
;;
;; See the appendix in the LPTP user manual for a full description.
;;
;; Installation:
;;
;; Include the following into your `.emacs' file (change the path name):
;;
;;      (autoload 'lptp-mode "/home/staerk/lptp/etc/lptp-mode" 
;;	  "Major mode for editing formal proofs" t)
;;
;;	(setq auto-mode-alist
;;	      (cons '("\\.pr$" . lptp-mode) auto-mode-alist))
;;
;; Edit the variables `prolog-program-name' and `lptp-start-string'
;; below.
;;
;; Usage:
;;
;; Press shift-control-mouse-1 for the popup menu (in GNU Emacs).
;;
;; A double click with the left mouse button selects the current formula
;; or the current proof step and copies it into the kill ring.
;;
;; From the Elisp manual:
;;
;;   Please do not define C-c <letter> as a key in your major
;;   modes. These sequences are reserved for users; they are the only
;;   sequences reserved for users, so we cannot do without them.
;; 
;;   Instead, define sequences consisting of C-c followed by a
;;   non-letter. These sequences are reserved for major modes.
;;
;;   Changing all the major modes in Emacs 18 so they would follow this
;;   convention was a lot of work. Abandoning this convention would
;;   waste that work and inconvenience the users.
;;
;; LPTP: "I do it. I define C-c i <letter> commands."


;;; Code:

(defvar prolog-program-name "/usr/local/bin/sicstus"
  "Program name for invoking an inferior Prolog process.")

(defvar prolog-start-file nil
  "Input from this file is sent to the inferior Prolog process.")

(defvar prolog-switch ""
  "The arguments for the Prolog program")

(defvar lptp-start-string "load('/home/staerk/lptp/bin/lptp').\n"
  "The Prolog command to load the LPTP system into Prolog.")

(defvar lptp-running-xemacs (string-match "XEmacs\\|Lucid" emacs-version)
  "Are we running XEmacs?")

(defvar lptp-syntax-table nil
  "Syntax table used while in LPTP mode.")

(defvar lptp-abbrev-table nil
  "Abbrev table used while in LPTP mode.")

(define-abbrev-table 'lptp-abbrev-table ())

(if lptp-syntax-table
    ()
  (setq lptp-syntax-table (make-syntax-table))
  (modify-syntax-entry ?,  "."    lptp-syntax-table)
  (modify-syntax-entry ?.  "."    lptp-syntax-table)
  (modify-syntax-entry ?:  "_"    lptp-syntax-table)
  (modify-syntax-entry ?|  "."    lptp-syntax-table)
  (modify-syntax-entry ?\; "."    lptp-syntax-table)
  (modify-syntax-entry ?!  "."    lptp-syntax-table)
  (modify-syntax-entry ?_  "_"    lptp-syntax-table)
  (modify-syntax-entry ?#  "_"    lptp-syntax-table)
  (modify-syntax-entry ?$  "_"    lptp-syntax-table)
  (modify-syntax-entry ?&  "_"    lptp-syntax-table)
  (modify-syntax-entry ?+  "_"    lptp-syntax-table)
  (modify-syntax-entry ?*  "_ 23" lptp-syntax-table)
  (modify-syntax-entry ?/  "_ 14" lptp-syntax-table)
  (modify-syntax-entry ?-  "_"    lptp-syntax-table)
  (modify-syntax-entry ?<  "_"    lptp-syntax-table)
  (modify-syntax-entry ?=  "_"    lptp-syntax-table)
  (modify-syntax-entry ?>  "_"    lptp-syntax-table)
  (modify-syntax-entry ?@  "_"    lptp-syntax-table)
  (modify-syntax-entry ?^  "_"    lptp-syntax-table)
  (modify-syntax-entry ?~  "_"    lptp-syntax-table)
  (modify-syntax-entry ?\\ "_"    lptp-syntax-table)
  (modify-syntax-entry ??  "'"    lptp-syntax-table)
  (modify-syntax-entry ?%  "<"    lptp-syntax-table)
  (modify-syntax-entry ?\" "\""   lptp-syntax-table)
  (modify-syntax-entry ?'  "\""   lptp-syntax-table)
  (modify-syntax-entry ?`  "\""   lptp-syntax-table))

(defvar lptp-keymap nil
  "Keymap for LPTP mode.")

(defun lptp-commands (map)
  (define-key map "\177"     'backward-delete-char-untabify)
  (define-key map "\C-c\C-@" 'lptp-mark-formula)
  (define-key map "\C-c\C-a" 'lptp-beginning-of-formula)
  (define-key map "\C-c\C-e" 'lptp-end-of-formula)
  (define-key map "\C-c\C-m" 'lptp-mark-fact)
  (define-key map "\C-c\C-n" 'lptp-next-formula)
  (define-key map "\C-c\C-p" 'lptp-previous-formula)
  (define-key map "\C-ci["   'lptp-insert-brackets)
  (define-key map "\C-cia"   'lptp-tactic-auto)
  (define-key map "\C-cib"   'lptp-tactic-debug)
  (define-key map "\C-cic"   'lptp-tactic-case)
  (define-key map "\C-cid"   'lptp-definition)
  (define-key map "\C-cie"   'lptp-tactic-elim)
  (define-key map "\C-cif"   'lptp-tactic-fact)
  (define-key map "\C-cig"   'lptp-get)
  (define-key map "\C-cii"   'lptp-tactic-ind)
  (define-key map "\C-cil"   'lptp-list-facts)
  (define-key map "\C-cin"   'lptp-send-no)
  (define-key map "\C-cim"   'lptp-mark-assumption)
  (define-key map "\C-cio"   'lptp-tactic-comp)
  (define-key map "\C-ciq"   'lptp-tactic-indqf)
  (define-key map "\C-cir"   'lptp-replace-ff-by-gap)
  (define-key map "\C-cis"   'lptp-save-send-buffer)
  (define-key map "\C-cit"   'lptp-tactic-tot)
  (define-key map "\C-ciu"   'lptp-tactic-unfold)
  (define-key map "\C-cix"   'lptp-tactic-ex)
  (define-key map "\C-ciy"   'lptp-send-yes)
  (define-key map "\C-ci~"   'lptp-backup-buffer)
  (define-key map "\n"       'newline-and-indent))

(defvar lptp-menu-map nil
  "Menu keymap for LPTP mode in GNU Emacs.")

(if (or lptp-menu-map lptp-running-xemacs)
    ()
  (let ((map (make-sparse-keymap "LPTP menu")))
    (setq lptp-menu-map map)
    (fset 'lptp-menu map)
    (define-key map [quit]    '("Quit LPTP".        lptp-quit))
    (define-key map [run]     '("Run LPTP".         run-lptp-other-frame))
    (define-key map [sep4]    '("--"))
    (define-key map [backup]  '("Backup buffer".    lptp-backup-buffer))
    (define-key map [bracket] '("Insert brackets".  lptp-insert-brackets))
    (define-key map [mark]    '("Mark formula".     lptp-mark-assumption))
    (define-key map [sep3]    '("--"))
    (define-key map [debug]   '("Debug".            lptp-tactic-debug))
    (define-key map [list]    '("List facts".       lptp-list-facts))
    (define-key map [def]     '("Print definition". lptp-definition))
    (define-key map [sep2]    '("--"))
    (define-key map [unfold]  '("Tactic: unfold".   lptp-tactic-unfold))
    (define-key map [tot]     '("Tactic: tot".      lptp-tactic-tot))
    (define-key map [indqf]   '("Tactic: indqf".    lptp-tactic-indqf))
    (define-key map [ind]     '("Tactic: ind".      lptp-tactic-ind))
    (define-key map [fact]    '("Tactic: fact".     lptp-tactic-fact))
    (define-key map [ex]      '("Tactic: ex".       lptp-tactic-ex))
    (define-key map [elim]    '("Tactic: elim".     lptp-tactic-elim))
    (define-key map [comp]    '("Tactic: comp".     lptp-tactic-comp))
    (define-key map [case]    '("Tactic: case".     lptp-tactic-case))
    (define-key map [auto]    '("Tactic: auto".     lptp-tactic-auto))
    (define-key map [sep1]    '("--"))
    (define-key map [get]     '("Get output".       lptp-get))
    (define-key map [send]    '("Send buffer".      lptp-save-send-buffer))))

(if lptp-keymap
    ()
  (setq lptp-keymap (make-sparse-keymap))
  (lptp-commands lptp-keymap)
  (if lptp-running-xemacs
      ()
    (define-key lptp-keymap [menu-bar] (make-sparse-keymap))
    (define-key lptp-keymap [menu-bar lptp]
      (cons "LPTP" lptp-menu-map))
    (define-key lptp-keymap [double-down-mouse-1] 'lptp-mark-formula)
    (define-key lptp-keymap [double-mouse-1] 'lptp-mark-formula)
    (define-key lptp-keymap [S-C-down-mouse-1] 'lptp-menu)))

(defvar lptp-xemacs-menubar-menu
  '("LPTP"
    ["Send buffer"      lptp-save-send-buffer t]
    ["Get output"       lptp-get t]
    "---"
    ["Tactic: auto"     lptp-tactic-auto t]
    ["Tactic: case"     lptp-tactic-case t]
    ["Tactic: comp"     lptp-tactic-comp t]
    ["Tactic: elim"     lptp-tactic-elim t]
    ["Tactic: ex"       lptp-tactic-ex t]
    ["Tactic: fact"     lptp-tactic-fact t]
    ["Tactic: ind"      lptp-tactic-ind t]
    ["Tactic: indqf"    lptp-tactic-indqf t]
    ["Tactic: tot"      lptp-tactic-tot t]
    ["Tactic: unfold"   lptp-tactic-unfold t]
    "---"
    ["Print definition" lptp-definition t]
    ["List facts"       lptp-list-facts t]
    ["Debug"            lptp-tactic-debug t]
    "---"
    ["Mark formula"     lptp-mark-assumption t]
    ["Insert brackets"  lptp-insert-brackets t]
    ["Backup buffer"    lptp-backup-buffer t]
    "---"
    ["Run LPTP"         run-lptp-other-frame t]
    ["Quit LPTP"        lptp-quit t]))

(defun lptp-xemacs-double-click (event count)
  (if (or (/= (event-button event) 1)
	  (/= count 2))
      nil
    (lptp-mark-formula) t))

(defun lptp-variables ()
  (set-syntax-table lptp-syntax-table)
  (setq local-abbrev-table lptp-abbrev-table)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'lptp-indent-line)
  (make-local-variable 'comment-start)
  (setq comment-start "%")
  (make-local-variable 'comment-end)
  (setq comment-end "")
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(lptp-font-lock-keywords t))
  (make-local-variable 'version-control)
  (setq version-control t)
  (make-local-variable 'kept-new-versions)
  (setq kept-new-versions 5))

(defun lptp-mode ()
  "Major mode for editing formal proofs in LPTP.
Press control-shift-left-mouse to obtain the popup menu.

Special commands:
\\{lptp-keymap}
Turning on LPTP mode calls the value of the variable `lptp-mode-hook',
if that value is non-nil."
  (interactive)
  (kill-all-local-variables)
  (use-local-map lptp-keymap)
  (setq mode-name "LPTP")
  (setq major-mode 'lptp-mode)
  (lptp-variables)
  (if (and lptp-running-xemacs (featurep 'menubar))
      (progn
	(set-buffer-menubar current-menubar)
	(add-submenu nil lptp-xemacs-menubar-menu)
	(make-local-variable 'mouse-track-click-hook)
	(add-hook 'mouse-track-click-hook 'lptp-xemacs-double-click)))
  (run-hooks 'lptp-mode-hook))

(defvar inferior-lptp-keymap nil)

(defun inferior-lptp-mode ()
  "Major mode for interacting with an inferior LPTP process.

The following commands are available:
\\{inferior-lptp-keymap}

Entry to this mode calls the value of `lptp-mode-hook' with no arguments,
if that value is non-nil.  Likewise with the value of `comint-mode-hook'.

You can send text to the inferior Prolog from other buffers
using the commands `send-region', `send-string'.

Return at end of buffer sends line as input.
Return not at end copies rest of line to end and sends it.
\\[comint-kill-input] and \\[backward-kill-word] are kill commands,
imitating normal Unix input editing.
\\[comint-interrupt-subjob] interrupts the shell or its current subjob if any.
\\[comint-stop-subjob] stops. \\[comint-quit-subjob] sends quit signal."
  (interactive)
  (require 'comint)
  (comint-mode)
  (setq major-mode 'inferior-lptp-mode
	mode-name "Inferior LPTP"
	comint-prompt-regexp "^| [ ?][- ] *")
  (lptp-variables)
  (if inferior-lptp-keymap nil
    (setq inferior-lptp-keymap (copy-keymap comint-mode-map))
    (lptp-commands inferior-lptp-keymap))
  (use-local-map inferior-lptp-keymap)
  (run-hooks 'lptp-mode-hook))

(defun run-lptp ()
  "Run an inferior LPTP process in the buffer *lptp*."
  (interactive)
  (require 'comint)
  (split-window-vertically)
  (other-window 1)
  (switch-to-buffer
   (make-comint
    "lptp" prolog-program-name prolog-start-file prolog-switch))
  (inferior-lptp-mode)
  (process-send-string "lptp" lptp-start-string))

(defun run-lptp-other-frame ()
  "Run an inferior LPTP process in a new frame."
  (interactive)
  (require 'comint)
  (switch-to-buffer-other-frame
   (make-comint
    "lptp" prolog-program-name prolog-start-file prolog-switch))
  (inferior-lptp-mode)
  (process-send-string "lptp" lptp-start-string))

(defun lptp-quit ()
  "Quit the LPTP process."
  (interactive)
  (process-send-string "lptp" "halt.\n")
  (kill-buffer "*lptp*"))

(defun lptp-save-send-buffer ()
  "Save buffer and send it to the LPTP process."
  (interactive)
  (save-buffer)
  (process-send-string "lptp" (format "exec('%s').\n" buffer-file-name)))

(defun lptp-backup-buffer ()
  "Save buffer and make the previous version into a backup file."
  (interactive)
  (save-buffer 16))

(defun lptp-definition (beg end)
  "Display the definition of the region in the *lptp* buffer."
  (interactive "r")
  (let ((string (buffer-substring beg end)))
    (process-send-string "lptp" (format "def(%s).\n" string))))

(defun lptp-mark-assumption (beg end)
  "Send the region as marked assumption to the *lptp* buffer."
  (interactive "r")
  (let ((string (buffer-substring beg end)))
    (process-send-string "lptp" (format "mark(%s).\n" string))))

(defun lptp-list-facts (beg end)
  "List all theorems about the region in the *lptp* buffer."
  (interactive "r")
  (let ((string (buffer-substring beg end)))
    (process-send-string "lptp" (format "facts(%s).\n" string))))

(defun lptp-send-yes ()
  "Send `y' to the LPTP process"
  (interactive)
  (process-send-string "lptp" "y\n"))

(defun lptp-send-no ()
  "Send `n' to the LPTP process"
  (interactive)
  (process-send-string "lptp" "n\n"))

(defun lptp-end-of-formula ()
  "Move point to the end of the current formula."
  (interactive)
  (skip-syntax-forward " ")
  (while (not (memq (following-char) '(?\) ?, ?. ?\] 0)))
    (forward-sexp)
    (skip-syntax-forward " "))
  (skip-syntax-backward " "))

(defun lptp-beginning-of-formula ()
  "Move point to the beginning of the current formula."
  (interactive)
  (skip-chars-backward " \t")
  (if (eq (preceding-char) ?,) (backward-char 1))
  (skip-syntax-backward " ")
  (while (not (memq (preceding-char) '(?\( ?, ?. ?\[ 0)))
    (backward-sexp)
    (skip-syntax-backward " "))
  (skip-syntax-forward " "))

(defun lptp-next-formula ()
  "Move point to the beginning of the next formula."
  (interactive)
  (lptp-end-of-formula)
  (skip-syntax-forward " ")
  (if (memq (following-char) '(?, ?.)) (forward-char 1))
  (skip-syntax-forward " "))

(defun lptp-previous-formula ()
  "Move point to the beginning of the previous formula."
  (interactive)
  (lptp-beginning-of-formula)
  (skip-syntax-backward " ")
  (if (memq (preceding-char) '(?, ?.)) (backward-char 1))
  (lptp-beginning-of-formula))

(defun lptp-mark-formula ()
  "Put point at beginning and mark at end of the formula."
  (interactive)
  (push-mark (point))
  (let ((beg (progn (lptp-beginning-of-formula) (point)))
	(end (progn (lptp-end-of-formula) (point)))
	;; cf. copy-region-as-kill in simple.el
	(this-command nil))
    (push-mark end nil t)
    (goto-char beg)
    (copy-region-as-kill beg end)))

(defun lptp-mark-fact ()
  "Put point at beginning and mark at end of the fact."
  (interactive)
  (push-mark (point))
  (search-forward ").")
  (forward-line)
  (push-mark (point) nil t)
  (search-backward ":-"))

(defun lptp-replace-ff-by-gap ()
  "Replace `ff by gap' by the previous formula and send the buffer."
  (interactive)
  (let ((beg2 (progn (lptp-beginning-of-formula) (point)))
	(end2 (progn (lptp-end-of-formula) (point)))
	(beg1 (progn (lptp-previous-formula) (point)))
	(end1 (progn (lptp-end-of-formula) (point))))
       (goto-char beg2)
       (delete-region beg2 end2)
       (insert (buffer-substring beg1 end1))
       (insert " by []") )
)

(defun lptp-tactic (string)
  ;; Inserts " by [<string>,l(<n>)]" at the end of the current formula,
  ;; where <n> is the indentation of the formula. If there exists already
  ;; a " by ...", it is replaced.
  (let ((beg (progn (lptp-beginning-of-formula) (point)))
	(end (progn (lptp-end-of-formula) (point))))
    (goto-char beg)
    (let ((indent (current-column)))
      (if (re-search-forward "\\s by\\s " end 0)
	  (delete-region (point) end)
	(insert " by "))
      (insert (format "[%s,l(%d)]" string indent)))
    (goto-char beg)
    (lptp-save-send-buffer)))

(defun lptp-tactic-fact ()
  "Try to prove the current formula by a known fact."
  (interactive)
  (lptp-tactic "fact"))

(defun lptp-tactic-ind ()
  "Try to prove the current formulas by induction."
  (interactive)
  (lptp-tactic "ind"))

(defun lptp-tactic-indqf ()
  "Try to prove the current formula by quantifier-free induction."
  (interactive)
  (lptp-tactic "indqf"))

(defun lptp-tactic-unfold (&optional more)
  "Try to prove the current formula by unfolding."
  (interactive "P")
  (if more (lptp-tactic "unfold,more")
    (lptp-tactic "unfold")))

(defun lptp-tactic-auto (&optional arg)
  "Try to prove the current formula automatically."
  (interactive "P")
  (let ((depth (or arg 5)))
    (lptp-tactic (format "auto(%d),more" depth))))

(defun lptp-tactic-case (&optional more)
  "Try to prove the current formula by case splitting."
  (interactive "P")
  (if more (lptp-tactic "case,more")
    (lptp-tactic "case")))

(defun lptp-tactic-ex (&optional more)
  "Try to prove the current formula by existential elimination."
  (interactive "P")
  (if more (lptp-tactic "ex,more")
    (lptp-tactic "ex")))

(defun lptp-tactic-elim (&optional more)
  "Try to prove the current formula by expanding a definition."
  (interactive "P")
  (if more (lptp-tactic "elim,more")
    (lptp-tactic "elim")))

(defun lptp-tactic-tot (&optional more)
  "Try to prove the current formula by case splitting on termination."
  (interactive "P")
  (if more (lptp-tactic "tot,more")
    (lptp-tactic "tot")))

(defun lptp-tactic-comp (&optional more)
  "Try to prove the current formula by taking a completion formula."
  (interactive "P")
  (if more (lptp-tactic "comp,more")
    (lptp-tactic "comp")))

(defun lptp-tactic-debug ()
  "Show the available formulas."
  (interactive)
  (lptp-tactic "debug"))

;; Assume that the buffer *lptp* looks as follows:
;; 
;; ---------- Buffer: *lptp* ----------
;; Some text.
;; ======
;;     Hello world!
;; ======
;; Some text not containing the magic equality sign string.
;; ---------- Buffer: *lptp* ----------
;; 
;; Then the function lptp-get replaces the region with the string
;; "Hello world!" from the buffer *lptp*.

(defun lptp-get ()
  "Replace the current formula by the output from the LPTP process."
  (interactive)
  (let ((beg (progn (lptp-beginning-of-formula) (point)))
	(list (lptp-element-of-list))
	(end (progn (lptp-end-of-formula) (point))))
    (delete-region beg end)
    (insert
     (save-excursion
       (set-buffer "*lptp*")
       (if (and list (lptp-output-is-list)) (lptp-remove-brackets))
       (buffer-substring
	(lptp-beginning-of-output)
	(lptp-end-of-output))))
    (goto-char beg)))

(defun lptp-element-of-list ()
  ;; Return t if the current formula is an element of a list and nil
  ;; otherwise.
  (save-excursion
    (skip-syntax-backward " ")
    (while (not (memq (preceding-char) '(?\( ?\[ ?. 0)))
      (backward-sexp)
      (skip-syntax-backward " "))
    (eq (preceding-char) ?\[)))

(defun lptp-beginning-of-output ()
  ;; Return the position of the beginning of the output in 
  ;; the *lptp* buffer.
  (goto-char (point-max))
  (search-backward "======")
  (search-backward "======")
  (forward-line)
  (skip-chars-forward " \t")
  (point))

(defun lptp-end-of-output ()
  ;; Return the position of the end of the output in 
  ;; the *lptp* buffer.
  (goto-char (point-max))
  (search-backward "======")
  (forward-line -1)
  (end-of-line)
  (point))

(defun lptp-output-is-list ()
  ;; Return t if the output in the *lptp* buffer is a list and nil
  ;; otherwise.
  (goto-char (lptp-beginning-of-output))
  (and (eq (following-char) ?\[)
       (progn
	 (forward-sexp)
	 (looking-at "\\s *======"))))

(defun lptp-remove-brackets ()
  ;; Remove the enclosing brackets of the output in the *lptp* buffer and
  ;; shift the output one column to the left.
  (let ((beg (progn
	       (goto-char (lptp-beginning-of-output))
	       (delete-char 1)
	       (point)))
	(end (progn
	       (goto-char (lptp-end-of-output))
	       (delete-backward-char 1)
	       (point))))
    (indent-rigidly beg end -1)))

(defun lptp-indent-line ()
  "Indent current line as line in a formal proof."
  (interactive)
  (let ((indent (+ (lptp-calculate-indent) (lptp-calculate-offset)))
	(pos (- (point-max) (point))))
    (if (= indent (current-indentation))
	(back-to-indentation)
      (beginning-of-line)
      (delete-region (point) (progn (skip-chars-forward " \t") (point)))
      (indent-to indent)
      (if (> (- (point-max) pos) (point))
	  (goto-char (- (point-max) pos))))))

(defun lptp-calculate-indent ()
  ;; This function is not yet optimal.
  (save-excursion
    (beginning-of-line)
    (skip-syntax-backward " ")
    (while (not (memq (preceding-char) '(?\( ?. ?\[ 0)))
      (backward-sexp)
      (skip-syntax-backward " "))
    (if (or (memq (preceding-char) '(?. 0))
	    (save-excursion (beginning-of-line) (looking-at "\\s *:-")))
	left-margin
      (let ((paren-depth
	     (let ((to (point))
		   (from (progn (beginning-of-line) (point))))
	       (car (parse-partial-sexp from to)))))
	(+ (current-indentation) paren-depth)))))

(defun lptp-calculate-offset ()
  ;; This function is not yet optimal.
  (save-excursion
    (beginning-of-line)
    (let ((offset 0) (by 0) (quant 0) (bound (point)))
      (skip-syntax-backward " ")
      (if (or (memq (preceding-char) '(?, ?\( ?\[ ?. 0))
	      (looking-at "\\s *\\s)"))
	  0
	(if (looking-at "\\s *by") (setq by 1))
	(if (looking-at "\\s *=>") (setq offset (1+ offset)))
	(lptp-beginning-of-formula)
	(if (or (looking-at "all") (looking-at "ex")) (setq quant 1))
	(while (< (point) bound)
	  (if (looking-at "\\s *by") (setq by 1))
	  (if (looking-at "\\s *=>") (setq offset (1+ offset)))
	  (forward-sexp)
	  (skip-syntax-forward " "))
	(+ offset (max by quant))))))

(defun lptp-insert-brackets ()
  "Insert a pair of brackets around the current formula and reindent it."
  (interactive)
  (lptp-beginning-of-formula)
  (insert "[")
  (let ((pos (point))
	(beg (progn (newline-and-indent) (point)))
	(end (progn (lptp-end-of-formula) (insert "]") (point))))
    (indent-region beg end nil)
    (goto-char pos)))

;; Use `M-x font-lock-mode' to fontify proofs.

(defvar lptp-font-lock-keywords
  '(("^:-[ ]*\\([a-z_]*\\)" 1 font-lock-keyword-face)
    ("lemma(\\([^,)]+\\)" 1 font-lock-reference-face) 
    ("corollary(\\([^,)]+\\)" 1 font-lock-reference-face) 
    ("theorem(\\([^,)]+\\)" 1 font-lock-reference-face)
    ("axiom(\\([^,)]+\\)" 1 font-lock-reference-face)
    ("definition_pred(\\([^,]+\\),\\([0-9]+\\)"
     (1 font-lock-reference-face) (2 font-lock-reference-face))
    ("definition_fun(\\([^,]+\\),\\([0-9]+\\)"
     (1 font-lock-reference-face) (2 font-lock-reference-face))
    ("elimination(\\([^,]+\\),\\([0-9]+\\)"
     (1 font-lock-reference-face) (2 font-lock-reference-face))
    ("introduction(\\([^,]+\\),\\([0-9]+\\)"
     (1 font-lock-reference-face) (2 font-lock-reference-face))
    ("by[ \n\t]+\\([a-z]*\\)" 1 font-lock-keyword-face)
    ("\\(axiom\\)(" 1 font-lock-keyword-face)
    ("\\(lemma\\)(" 1 font-lock-keyword-face)
    ("\\(corollary\\)(" 1 font-lock-keyword-face)
    ("\\(theorem\\)(" 1 font-lock-keyword-face)
    ("\\(assume\\)(" 1 font-lock-keyword-face)
    ("\\(cases\\)(" 1 font-lock-keyword-face)
    ("\\(case\\)(" 1 font-lock-keyword-face)
    ("\\(contra\\)(" 1 font-lock-keyword-face)
    ("\\(exist\\)(" 1 font-lock-keyword-face)
    ("\\(induction\\)(" 1 font-lock-keyword-face)
    ("\\(step\\)(" 1 font-lock-keyword-face)
    ("\\(indirect\\)(" 1 font-lock-keyword-face)
    ("\\(definition_fun\\)(" 1 font-lock-keyword-face)
    ("\\(definition_pred\\)(" 1 font-lock-keyword-face)
    ("! LPTP-[a-zA-Z]*" . font-lock-comment-face)
    ("by[ \n\t]+\\(gap\\)" 1 font-lock-comment-face t) ))

;;; lptp.el ends here

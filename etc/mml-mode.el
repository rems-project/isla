
(defvar isla-mml-mode-hook nil)

(defconst isla-mml-keywords
  '("accessor" "acyclic" "as" "assert"
    "declare" "define"
    "empty" "enum"
    "exists"
    "flag" "forall"
    "in" "include" "index"
    "let"
    "match"
    "relation"
    "set" "show"
    "unshow"
    "where"))

(defconst isla-mml-types
  '("Event" "bits" "bool"))

(defconst isla-mml-font-lock-keywords
  `((,(regexp-opt isla-mml-keywords 'symbols) . font-lock-keyword-face)
    (,(regexp-opt isla-mml-types 'symbols) . font-lock-type-face)
    ("~" . font-lock-negation-char-face)
    (": \\([a-zA-Z0-9_-]+\\)" 1 font-lock-type-face)
    ("enum \\([a-zA-Z0-9_-]+\\)" 1 font-lock-type-face)
    ("define \\([a-zA-Z0-9_-]+\\)" 1 font-lock-function-name-face)
    ("declare \\([a-zA-Z0-9_-]+\\)" 1 font-lock-function-name-face)
    ("let \\([a-zA-Z0-9_-]+\\)" 1 font-lock-function-name-face)
    ("accessor \\([a-zA-Z0-9_-]+\\)" 1 font-lock-function-name-face)))

(defconst isla-mml-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?> "." st)
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?- "w" st)
    (modify-syntax-entry ?\( ". 1n" st)
    (modify-syntax-entry ?\) ". 4" st)
    (modify-syntax-entry ?* ". 23n" st)
    st)
  "Syntax table for isla-mml-mode")

(defun isla-mml-mode ()
  "Major mode for editing Isla memory model files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table isla-mml-mode-syntax-table)
  (setq font-lock-defaults '(isla-mml-font-lock-keywords))
  (setq comment-start "(*")
  (setq comment-end "*)")
  (setq major-mode 'isla-mml-mode)
  (setq mode-name "Isla Memory Model")
  (run-hooks 'isla-mml-mode-hook))

(provide 'isla-mml-mode)

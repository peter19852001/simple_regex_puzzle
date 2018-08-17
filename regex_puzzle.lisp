(ql:quickload :cl-ppcre)
(defpackage :mit-regex-puzzle
  (:use :common-lisp :cl-ppcre))

(in-package :mit-regex-puzzle)

;;; The puzzle is a hexagonal grid with rows, left and right diagonals having regular
;;; expressions as constraints, and the goal is to fill in the hexagons such that
;;; all the regular expressions are satisfied.

;;; Here we solve a particular instance by constraint propagation and backtracking search.
;;; The instance is http://www.theonlineoasis.co.uk/regex/regex.html

;;; Representation of the grid, use a rectangular 2D array, but some cells are left empty.
;;; Each cell contains either
;;;   1. a character: which means the value is determined
;;;   2. a list of characters: the only possiblities at this cell
(defparameter *A-Z* '(#\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
                      #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z))
(defun empty-board ()
  (make-array '(13 13) :initial-element *A-Z*))

(defun cell-char (c) (if (characterp c) c #\_))
(defun board-char (b i j) (cell-char (aref b i j)))
(defun pr-cell (c) (format t "~A " (cell-char c)))
(defun pr-indent (n)
  (dotimes (i n) (format t " ")))
(defun row-start (i) (if (> i 6) (- i 6) 0))
(defun row-end (i) (if (< i 6) (+ i 7) 13)) ; end is exclusive
(defun col-start (i) (if (> i 6) (- i 6) 0))
(defun col-end (i) (if (< i 6) (+ i 7) 13)) ; end is exclusive
(defun diag-of (i j) (+ 6 (- j i)))
(defun diag-i (di) (if (> di 6) (- 18 di) 12))
(defun diag-j (di) (if (< di 6) (+ di 6)  12))
(defun pr-board (b)
  (dotimes (i 13)
    (pr-indent (abs (- 6 i)))
    (loop for j from (row-start i) below (row-end i) do
         (pr-cell (aref b i j)))
    (terpri)))
(defun copy-board (board)
  (let ((b (empty-board)))
    (dotimes (i 13)
      (dotimes (j 13)
        (setf (aref b i j) (aref board i j))))
    b))

(defparameter *string-buffer* (make-string 13 :initial-element #\_))
(defun get-str-at-row (board i &optional (out-str *string-buffer*))
  "Get the string at row i of the board, and put at out-str, and return the length."
  (let ((s (row-start i))
        (e (row-end i)))
    (do ((k 0 (1+ k))
         (ci s (1+ ci)))
        ((>= ci e) (- e s))
      (setf (char out-str k) (board-char board i ci)))))
(defun get-str-at-col (board j &optional (out-str *string-buffer*))
  "Get the string at column j of the board, and put at out-str, and return the length."
  (let ((s (col-start j))
        (e (col-end j)))
    (do ((k 0 (1+ k))
         (ci s (1+ ci)))
        ((>= ci e) (- e s))
      (setf (char out-str k) (board-char board ci j)))))
(defun get-str-at-diag (board di &optional (out-str *string-buffer*))
  "Get the string at diagonal di of the board, and put at out-str, and return the length."
  (do ((k 0 (1+ k))
       (i (diag-i di) (1- i))
       (j (diag-j di) (1- j)))
      ((or (< i 0) (< j 0)) k)
    (setf (char out-str k) (board-char board i j))))
;;; The constraints for rows, columns and diagonals. Order is important.
;;; Each constraint is a function of a string and length, that should return
;;; true if portion of the string satisfies the constraints, and returns false otherwise.
;;; Those with backreferences will be handled specially.
(defun relax-regex (str)
  "To transform the regex str to allow underscore(_) to stand for unknown, and match as much as it can.
Does NOT work for backreferences."
  (labels ((f (cs out)
             (if (null cs)
                 out
                 (let ((c (car cs)))
                   (cond ((member c *A-Z*)
                          (push #\[ out) (push #\_ out) (push c out) (push #\] out)
                          (f (cdr cs) out))
                         ((eql c #\[)
                          (push #\[ out)
                          (unless (eql (cadr cs) #\^)
                            (push #\_ out))
                          (do ((ls (cdr cs) (cdr ls)))
                              ((eql (car ls) #\])
                               (push #\] out)
                               (f (cdr ls) out))
                            (push (car ls) out)))
                         (t (push c out)
                            (f (cdr cs) out)))))))
    (coerce (nreverse (f (coerce str 'list) '())) 'string)))

(defun regex (str)
  (let ((re (cl-ppcre:create-scanner (relax-regex str))))
    #'(lambda (s L)
        (cl-ppcre:scan re s :end L))))
(defun no-constraint (s L) (declare (ignore s L)) t)
;; for regex using backreference, we use custom function
(defun complete-str (s L) (not (find #\_ s :end L)))
(defun special-handler (str handler)
  "Return a function that uses str as regex for checking if the whole string is filled,
 otherwise use the handler for checking. handler has the same signature as the constraint function."
  (let ((re (cl-ppcre:create-scanner str)))
    #'(lambda (s L)
        (if (complete-str s L)
            (cl-ppcre:scan re s :end L)
            (funcall handler s L)))))
;;;
(defun special-char-eql (&rest cs)
  "Allow underscore as wildcard to match any, others must be matched."
  (let ((x (find-if (lambda (c) (not (eql c #\_))) cs)))
    (or (not x)
        (every (lambda (c) (or (eql c #\_) (eql c x))) cs))))
(defun two-three-rep-L12 (s L)
  "For ^(...?)\\1*$"
  ;; assume L is 12
  (and (= L 12)
       (or (and (special-char-eql (char s 0) (char s 3) (char s 6) (char s  9))
                (special-char-eql (char s 1) (char s 4) (char s 7) (char s 10))
                (special-char-eql (char s 2) (char s 5) (char s 8) (char s 11)))
           (and (special-char-eql (char s 0) (char s 2) (char s 4) (char s 6) (char s 8) (char s 10))
                (special-char-eql (char s 1) (char s 3) (char s 5) (char s 7) (char s 9) (char s 11))))))
(defun p-two-rep (s L)
  "For ^P+(..)\\1.*$"
  (dotimes (i (- L 7) nil)
    (if (and (special-char-eql (char s (+ i 1)) (char s (+ i 3)))
             (special-char-eql (char s (+ i 2)) (char s (+ i 4)))
             (= (count-if (lambda (c) (or (eql c #\_) (eql c #\P))) s :end (1+ i))
                (1+ i)))
        (return t))))
(defun four-mirror (s L)
  "For ^.*(.)(.)(.)(.)\\4\\3\\2\\1.*$"
  (dotimes (i (- L 7) nil)
    (if (and (special-char-eql (char s (+ i 0)) (char s (+ i 7)))
             (special-char-eql (char s (+ i 1)) (char s (+ i 6)))
             (special-char-eql (char s (+ i 2)) (char s (+ i 5)))
             (special-char-eql (char s (+ i 3)) (char s (+ i 4))))
        (return t))))
(defun one-c-one-x-one (s L)
  "For ^.*(.)C\\1X\\1.*$"
  (dotimes (i (- L 4) nil)
    (if (and (special-char-eql #\C (char s (+ i 1)))
             (special-char-eql #\X (char s (+ i 3)))
             (special-char-eql (char s (+ i 0)) (char s (+ i 2)) (char s (+ i 4))))
        (return t))))
(defparameter *row-constraints*
  (vector
   (regex "^.*H.*H.*$")
   (regex "^(DI|NS|TH|OM)*$")
   (regex "^F.*[AO].*[AO].*$")
   (regex "^(O|RHH|MM)*$")
   #'no-constraint ;;(regex "^.*$")
   (regex "^C*MC(CCC|MM)*$")
   (regex "^[^C]*[^R]*III.*$")
   (special-handler "^(...?)\\1*$" #'two-three-rep-L12) ;;;
   (regex "^([^X]|XCC)*$")
   (regex "^(RR|HHH)*.?$")
   (regex "^N.*X.X.X.*E$")
   (regex "^R*D*M*$")
   (regex "^.(C|HH)*$")))
(defparameter *col-constraints*
  (vector
   (regex "^(ND|ET|IN)[^X]*$")
   (regex "^[CHMNOR]*I[CHMNOR]*$")
   (special-handler "^P+(..)\\1.*$" #'p-two-rep) ;;;
   (regex "^(E|CR|MN)*$")
   (regex "^([^MC]|MM|CC)*$")
   (regex "^[AM]*CM(RC)*R?$")
   #'no-constraint ;;(regex "^.*$")
   (regex "^.*PRR.*DDC.*$")
   (regex "^(HHX|[^HX])*$")
   (regex "^([^EMC]|EM)*$")
   (regex "^.*OXR.*$")
   (regex "^.*LR.*RL.*$")
   (regex "^.*SE.*UE.*$")))
(defparameter *diag-constraints*
  (vector
   (regex "^.*G.*V.*H.*$")
   (regex "^[CR]*$")
   (regex "^.*XEXM*$")
   (regex "^.*DD.*CCM.*$")
   (regex "^.*XHCR.*X.*$")
   (special-handler "^.*(.)(.)(.)(.)\\4\\3\\2\\1.*$" #'four-mirror) ;;;
   (regex "^.*(IN|SE|HI)$")
   (regex "^[^C]*MMM[^C]*$")
   (special-handler "^.*(.)C\\1X\\1.*$" #'one-c-one-x-one) ;;;
   (regex "^[CEIMU]*OH[AEMOR]*$")
   (regex "^(RX|[^R])*$")
   (regex "^[^M]*M[^M]*$")
   (regex "^(S|MM|HHH)*$")))
;;; Use *string-buffer* as buffer
(defun validate-row (board i)
  (let ((L (get-str-at-row board i)))
    (if (funcall (aref *row-constraints* i) *string-buffer* L) t nil)))
(defun validate-col (board i)
  (let ((L (get-str-at-col board i)))
    (if (funcall (aref *col-constraints* i) *string-buffer* L) t nil)))
(defun validate-diag (board i)
  (let ((L (get-str-at-diag board i)))
    (if (funcall (aref *diag-constraints* i) *string-buffer* L) t nil)))
(defun validate-board (board)
  (dotimes (i 13 t)
    (if (not (validate-row board i)) (return nil))
    (if (not (validate-col board i)) (return nil))
    (if (not (validate-diag board i)) (return nil))))

(defun validate-cell (board i j)
  (and (validate-row board i) (validate-col board j) (validate-diag board (diag-of i j))))
(defun can-put-at-cell (board i j x)
  "Try to put character x at cell (i . j). If ok, returns true. Otherwise returns false.
In either case, the cell (i . j) will be changed back to its original value."
  (let ((old (aref board i j)))
    (setf (aref board i j) x)
    (let ((r (validate-cell board i j)))
      (setf (aref board i j) old)
      r)))
(defun cell-possibilities (board i j poss)
  (let ((r '()))
    (dolist (c poss)
      (if (can-put-at-cell board i j c)
          (push c r)))
    r))
;;;;
;;; config: a board together with an order of the cells to try.
;;; Each cell is named by (i . j) pair, for row i and column j in the board.
;;; The order is maintained as a vector of list. Slot i stores the list of cells
;;;   which have i possibilities in the board.
(defun make-cell (i j) (cons i j))
(defun cell-i (c) (car c))
(defun cell-j (c) (cdr c))
(defun cell-ordering (board)
  (let ((v (make-array 27 :initial-element nil)))
    (dotimes (i 13)
      (loop for j from (row-start i) below (row-end i) do
           (let ((c (aref board i j)))
             (if (listp c)
                 (push (make-cell i j) (aref v (length c)))))))
    v))
(defun make-config (board)
  (cons board (cell-ordering board)))
(defun config-board (cfg) (car cfg))
(defun pr-config (cfg)
  (if cfg
      (pr-board (config-board cfg))
      (print "No possible configs.")))
(defun pop-next-cell-to-try! (cfg)
  "Return the next cell to try. Return nil if there is no next move.
The config itself is updated."
  (let ((ordering (cdr cfg)))
    (dotimes (i (length ordering) nil)
      (let ((ls (aref ordering i)))
        (if ls (return (pop (aref ordering i))))))))

(defun propagate-cells! (b cells-to-update)
  "For the cells in the list cells-to-update, assume their values are determined, propagate the constraints to other cells in the same row, column and diagonal.
In the process of propagating, if contradiction is found, returns nil. If other cells are reduced to one possibility, they will be also placed and propagated. Return the modified board."
  (let ((failed nil))
    (labels ((update-cell-possibilities (u v)
               (let ((c (aref b u v)))
                 (when (listp c)
                   (let ((nc (cell-possibilities b u v c)))
                     (cond ((null nc) (setf failed t))
                           ((null (cdr nc))
                            (push (make-cell u v) cells-to-update)
                            (setf (aref b u v) (car nc)))
                           (t (setf (aref b u v) nc))))))))
      (loop
         (if failed (return nil))
         (if (null cells-to-update) (return b))
         (let* ((cell (pop cells-to-update))
                (u (cell-i cell))
                (v (cell-j cell)))
           (loop for k from (row-start u) below (row-end u) never failed do (update-cell-possibilities u k)) ;; row
           (if failed (return nil))
           (loop for k from (col-start v) below (col-end v) never failed do (update-cell-possibilities k v)) ;; column
           (if failed (return nil))
           ;; diagonal
           (do ((du (diag-i (diag-of u v)) (1- du))
                (dv (diag-j (diag-of u v)) (1- dv)))
               ((or (< du 0) (< dv 0) failed))
             (update-cell-possibilities du dv))
           (if failed (return nil)))))))

(defun propagate-cell (board i j x)
  "Assuming can place x at cell (i . j), copy the board, and place x at cell (i . j), and propagate the constraints to other cells in the same row, column and diagonal.
In the process of propagating, if contradiction is found, returns nil. If other cells are reduced to one possibility, they will be also placed and propagated. Return the new board."
  (and (can-put-at-cell board i j x)
       (let ((b (copy-board board)))
         (setf (aref b i j) x)
         (propagate-cells! b (list (make-cell i j))))))

;;;; Not yet implemented the backtracking, but now can already obtain the full board
;;;;   by constraint propagation when given the cell (0 . 0) to be N,
;;;;   but when given only (0 . 2) is P, 5 cells would still be unfilled.
(defun initial-config (board)
  "Need only cause each cell to be checked at least once. Returns the config of the new board if ok. Otherwise returns nil."
  (let ((b (copy-board board))
        (cells-to-check '()))
    (dotimes (i 13)
      (push (make-cell i (row-start i)) cells-to-check))
    (let ((nb (propagate-cells! b cells-to-check)))
      (if nb (make-config nb) nil))))

;;;;
(defun puzzle-dfs (cfg)
  "Use quite naive Depth First Search to solve the puzzle. But since the constraint propagation does a good job, so this search need not be very clever.
Returns a solved board it OK. Returns nil otherwise."
  (if (null cfg)
      nil
      (let ((move (pop-next-cell-to-try! cfg))
            (board (config-board cfg)))
        (cond (move (let ((poss (aref board (cell-i move) (cell-j move))))
                      (cond ((null poss) nil)
                            ((characterp poss) (puzzle-dfs cfg))
                            (t (dolist (c poss nil)
                                 (let* ((nb (propagate-cell board (cell-i move) (cell-j move) c))
                                        (nc (if nb (puzzle-dfs (make-config nb)) nil)))
                                   (if nc (return nc))))))))
              ((validate-board board) board)
              (t nil)))))
;;;;;

(defparameter *test-c* (initial-config (empty-board)))
(defparameter *test-c1* (puzzle-dfs *test-c*))
(if *test-c1* (pr-board *test-c1*) (print "No configs."))
;;; One possible board configuration, in fact it should be the only possible one.
;;;
;;;       N H P E H A S 
;;;      D I O M O M T H 
;;;     F O X N X A X P H 
;;;    M M O M M M M R H H 
;;;   M C X N M M C R X E M 
;;;  C M C C C C M M M M M M 
;;; H R X R C M I I I H X L S 
;;;  O R E O R E O R E O R E 
;;;   V C X C C H H M X C C 
;;;    R R R R H H H R R U 
;;;     N C X D X E X L E 
;;;      R R D D M M M M 
;;;       G C C H H C C 
;;;;;

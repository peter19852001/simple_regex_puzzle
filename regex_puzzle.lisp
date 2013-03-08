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
(defun pr-board (b)
  (dotimes (i 7)
    (pr-indent (- 6 i))
    (dotimes (j (+ 7 i))
      (pr-cell (aref b i j)))
    (terpri))
  (dotimes (i 6)
    (pr-indent (1+ i))
    (dotimes (j (- 12 i))
      (pr-cell (aref b (+ i 7) j)))
    (terpri)))

(defparameter *string-buffer* (make-string 13 :initial-element #\_))
(defun row-start (i) (if (> i 6) (- i 6) 0))
(defun row-end (i) (if (< i 6) (+ i 7) 13)) ; end is exclusive
(defun col-start (i) (if (> i 6) (- i 6) 0))
(defun col-end (i) (if (< i 6) (+ i 7) 13)) ; end is exclusive
(defun diag-of (i j) (+ 6 (- j i)))
(defun get-str-at-row (board i &optional (out-str *string-buffer*))
  "Get the string at row i of the board, and put at out-str, and return the length."
  (let ((s (row-start i))
	(e (row-end i)))
    (do ((k 0 (1+ k))
	 (ci s (1+ ci)))
	((>= ci e) (- e s))
      (setf (char *string-buffer* k) (board-char board i ci)))))
(defun get-str-at-col (board j &optional (out-str *string-buffer*))
  "Get the string at column j of the board, and put at out-str, and return the length."
  (let ((s (col-start j))
	(e (col-end j)))
    (do ((k 0 (1+ k))
	 (ci s (1+ ci)))
	((>= ci e) (- e s))
      (setf (char *string-buffer* k) (board-char board ci j)))))
(defun get-str-at-diag (board di &optional (out-str *string-buffer*))
  "Get the string at diagonal di of the board, and put at out-str, and return the length."
  (do ((k 0 (1+ k))
       (i (if (> di 6) (- 18 di) 12) (1- i))
       (j (if (< di 6) (+ di 6)  12) (1- j)))
      ((or (< i 0) (< j 0)) k)
    (setf (char *string-buffer* k) (board-char board i j))))
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
   (regex "^(RR|HHH).*.?$")
   (regex "^N.*X.X.X.*E$")
   (regex "^R*D*M*$")
   (regex "^.(C|HH)*$")))
(defparameter *col-constraints*
  (vector
   (regex "^(ND|ET|IN)[^X]*$")
   (regex "^[CHMNOR]*I[CHMNOR]$")
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
   (regex "^.*SU.*UE.*$")))
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
;;;;

;;;;

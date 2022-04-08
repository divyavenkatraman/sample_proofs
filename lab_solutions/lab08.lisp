#|

Lab 8. Termination and Measure Functions.

In this lab we will prove termination using measure functions. The
exercises bring up many interesting issues, so make sure you know how
to prove the functions below terminate.

Your primary goal is to come up with paper-and-pencil proofs, not
ACL2s proofs. We provide ACL2s definitions so that you can explore the
functions, e.g., you can trace definitions as per the lecture notes on
debugging & understanding code.

Prove that the following functions are terminating by coming up with
an appropriate measure function and proving that it is a measure
function.

|#

(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-defunc-generate-generalize-rules nil)
(set-gag-mode nil)
(set-ignore-ok t)

; Prove that this function is terminating.  Can you do so using
; measure functions or do you have to use generalized measure
; functions?
(definec app?-t2 (x :tl y :tl acc :tl) :tl
  (if (endp x)
      (if (endp y)
          acc
        (app?-t2 x (rest y) (cons (first y) acc)))
    (app?-t2 (rest x) y (cons (first x) acc))))

; Prove that this function is terminating.  Can you do so using
; measure functions or do you have to use generalized measure
; functions?
(definec app?-t3 (x :tl y :tl acc :tl) :tl
  (cond ((and (endp x) (endp y)) acc)
        ((endp x) (app?-t3 x (rest y) (cons (first y) acc)))
        ((endp y) (app?-t3 (rest x) y (cons (first x) acc)))
        (t (app?-t3 x nil (app?-t3 nil y acc)))))

; Prove that this function is terminating.  Can you do so using
; measure functions or do you have to use generalized measure
; functions?
(definec app?-t4 (x :tl y :tl acc :tl) :tl
  (cond ((and (endp x) (endp y)) acc)
        ((endp x) (app?-t4 x (rest y) (cons (first y) acc)))
        ((endp y) (app?-t4 y x acc))
        (t (app?-t4 x nil (app?-t4 acc nil y)))))

; Prove that this function is terminating.  
(definec flip (x :all) :all
  (if (atom x)
      x
    (cons (flip (cdr x))
          (flip (car x)))))

; Here is a function that you may find useful when constructing a
; measure function for magnitude. It is non-recursive, so you don't
; have to prove termination.

(definec ceil (x :non-neg-rational) :nat
  (ceiling x 1))

; Here are some tests showing how ceil works.

(check= (ceil 11) 11)
(check= (ceil 10/3) 4)
(check= (ceil 10/101) 1)

:program
; ACL2s needs help to prove termination of the following definitions.

(definec magnitude (x :non-neg-rational) :int
  (cond ((equal x 0) 0)
        ((>= x 10) (+ 1 (magnitude (/ x 10))))
        ((< x 1) (* -1 (magnitude (/ 1 x))))
        (t 1)))

; To come up with a measure, you have to understand how magnitude
; works, so one way to do that is to trace it and try running it on
; examples.

(trace$ magnitude)

(magnitude 20)
(magnitude 200000)
(magnitude 200000000000)
(magnitude 1/20)
(magnitude 1/200000)
(magnitude 1/200000000000)

; Now, come up with a measure function and prove it correct.


#|

If you want to debug your measure functions using ACL2s, then use the
instructions at the end of lab07.

|#

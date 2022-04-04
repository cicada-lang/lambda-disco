---
title: Typing Encoding of Natural Number with Self Type
---

# Self type

Remember that `ind-Nat` take `target` as an explicit argument,
because we want to infer application of `ind-Nat`.

```scheme
(claim ind-Nat
  (Pi ((target Nat)
       (motive (Pi ((target Nat)) Type))
       (base (motive zero))
       (step (Pi ((prev Nat)
                  (almost (motive prev)))
               (motive (add1 prev)))))
    (motive target)))

(define (ind-Nat target motive base step)
  (target motive base step))

;; NOTE Maybe we should also allow the following syntax.

(claim ind-Nat
  (Pi ((target Nat)
       ((motive (target Nat)) Type)
       (base (motive zero))
       ((step (prev Nat)
              (almost (motive prev)))
        (motive (add1 prev))))
    (motive target)))

(claim (ind-Nat (target Nat)
         ((motive (target Nat)) Type)
         (base (motive zero))
         ((step (prev Nat)
                (almost (motive prev)))
          (motive (add1 prev))))
  (motive target))
```

We already know `(ind-Nat zero motive)`
should be `(lambda (base step) base)`,
thus we have an equation about `zero`,
let's try to solve `zero` from this equation.

```scheme
(claim (ind-Nat zero motive)
  (Pi ((base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive zero)))

(assert-equal
  (ind-Nat zero motive)
  (lambda (base step) (zero motive base step))
  (lambda (base step) base))

(define zero (lambda (motive base step) base))

(claim zero
  (Pi ((motive (-> Nat Type))
       (base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive zero)))
```

The type of `zero` is `Nat`,
thus we have:

```scheme
(define Nat
  (Pi ((motive (-> Nat Type))
       (base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive target)))
```

But the `target` is a free variable.

```scheme
(define (add1 prev)
  (lambda (motive base step)
    (step prev (prev motive base step))))

(claim add1
  (-> Nat Nat)
  (Pi ((prev Nat)
       (motive (-> Nat Type))
       (base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive (add1 prev))))
```

It seems we are defining one `Nat` for each `target`.

Here comes **self type**.

```scheme
(define Nat
  (Self (target)
    (Pi ((motive (-> Nat Type))
         (base (motive zero))
         (step (Pi ((prev Nat)
                    (almost (motive prev)))
                 (motive (add1 prev)))))
      (motive target))))
```

Note that, in the defining of `Nat`,
`zero` and `add1` occurred,
but the type of `zero` is `Nat`.

This means we must define them as a group.

- [Wikipedia / Impredicativity](https://en.wikipedia.org/wiki/Impredicativity)

- In the _System S_ of Fu Peng,
  the definition of `Nat` can referece `zero` and `add1`
  recursively.

  - Called "clusure" by Fu Peng, and is used as part of the context.

# Judgment of self type

```scheme
(define-judgment (Check Ctx Exp Exp)
  (axiom
   (check ctx Prop Type))

  (start
   (check ctx A Sort)
   (check (ctx x A) x A))

  (weakening
   (check ctx A B)
   (check ctx C Sort)
   (check (ctx x C) A B))

  (application
   (check ctx C (Pi ((x A)) B))
   (check ctx a A)
   (check ctx (C a) (subst B x a)))

  (conversion
   (check ctx A B)
   (beta-equal B B')
   (check ctx B' Sort)
   (check ctx A B'))

  (product
   (Check ctx A SortLeft)
   (Check (extend ctx x A) B SortRight)
   (Check ctx (Pi ((x A)) B) SortRight))

  (abstraction
   (Check ctx A SortLeft)
   (Check (extend ctx x A) B SortRight)
   (Check (extend ctx x A) b B)
   (Check ctx (lambda ((x A)) b) (Pi ((x A)) B)))

  (self-abstraction
   (Check ctx x (subst B target x))
   (Check ctx x (Self (target) B)))

  (self-application
   (Check ctx x (Self (target) B))
   (Check ctx x (subst B target x))))
```

# Example deductions

Check `zero` is `Nat`.

- The syntax `(deduction)` is linear.

  - We can do this because the arity of a rule is fixed.

  - Thinking about constructing a stack of
    goals and application of rules,
    then execute them reversely.

```scheme
(deduction
 (Check (ctx)
   zero
   (Self (target)
     (Pi ((motive (-> Nat Type))
          (base (motive zero))
          (step (Pi ((prev Nat))
                  (-> (motive prev)
                      (motive (add1 prev))))))
       (motive target))))

 (=> Check self-abstraction)

 (Check (ctx)
   zero
   (Pi ((motive (-> Nat Type))
        (base (motive zero))
        (step (Pi ((prev Nat))
                (-> (motive prev)
                    (motive (add1 prev))))))
     (motive zero)))

 (=> definition of zero)

 (Check (ctx)
   (lambda (motive base step) base)
   (Pi ((motive (-> Nat Type))
        (base (motive zero))
        (step (Pi ((prev Nat))
                (-> (motive prev)
                    (motive (add1 prev))))))
     (motive zero)))

 (=> Check abstraction)

 (Check (ctx ((motive (-> Nat Type))
              (base (motive zero))
              (step (Pi ((prev Nat))
                      (-> (motive prev)
                          (motive (add1 prev)))))))
   (motive zero)
   Type)

 (=> Check application)

 (Check (ctx ((motive (-> Nat Type))
              (base (motive zero))
              (step (Pi ((prev Nat))
                      (-> (motive prev)
                          (motive (add1 prev)))))))
   motive
   (-> Nat Type))

 (=> Check lookup)

 (Check (ctx ((motive (-> Nat Type))
              (base (motive zero))
              (step (Pi ((prev Nat))
                      (-> (motive prev)
                          (motive (add1 prev)))))))
   zero Nat)

 ;; NOTE Why `zero` is of type `Nat` here?
 (=> How?)

 (Check (ctx ((motive (-> Nat Type))
              (base (motive zero))
              (step (Pi ((prev Nat))
                      (-> (motive prev)
                          (motive (add1 prev)))))))
   base
   (motive zero))

 (=> Check lookup))
```

Check `add1` is `(-> Nat Nat)`.

```scheme
(deduction
 (Check (ctx) add1 (-> Nat Nat))

 (=> definition of add1 and Nat)

 (Check (ctx)
   (lambda (prev)
     (lambda (motive base step)
       (step prev (prev motive base step))))
   (-> Nat
       (Self (target)
         (Pi ((motive (-> Nat Type))
              (base (motive zero))
              (step (Pi ((prev Nat))
                      (-> (motive prev)
                          (motive (add1 prev))))))
           (motive target)))))

 (=> Check abstraction)

 (Check (ctx (prev Nat))
   (lambda (motive base step)
     (step prev (prev motive base step)))
   (Self (target)
     (Pi ((motive (-> Nat Type))
          (base (motive zero))
          (step (Pi ((prev Nat))
                  (-> (motive prev)
                      (motive (add1 prev))))))
       (motive target))))

 (=> Check self-abstraction)

 (Check (ctx (prev Nat))
   (lambda (motive base step)
     (step prev (prev motive base step)))
   (Pi ((motive (-> Nat Type))
        (base (motive zero))
        (step (Pi ((prev Nat))
                (-> (motive prev)
                    (motive (add1 prev))))))
     (motive (lambda (motive base step)
               (step prev (prev motive base step))))))

 (=> Check abstraction)

 (Check (ctx (prev Nat)
             (motive (-> Nat Type))
             (base (motive zero))
             (step (Pi ((prev Nat))
                     (-> (motive prev)
                         (motive (add1 prev))))))
   ((step prev) (prev motive base step))
   (motive (lambda (motive base step)
             (step prev (prev motive base step)))))

 (=> Check application)

 (Check (ctx (prev Nat)
             (motive (-> Nat Type))
             (base (motive zero))
             (step (Pi ((prev Nat))
                     (-> (motive prev)
                         (motive (add1 prev))))))
   (step prev)
   (-> (motive prev)
       (motive (add1 prev)))
   (comments
     This is where target (the self value) is used.
     (assert-equal
       (add1 prev)
       (lambda (motive base step)
         (step prev (prev motive base step))))))

 (=> Check application)

 (Check (ctx (prev Nat)
             (motive (-> Nat Type))
             (base (motive zero))
             (step (Pi ((prev Nat))
                     (-> (motive prev)
                         (motive (add1 prev))))))
   step
   (Pi ((prev Nat))
     (-> (motive prev)
         (motive (add1 prev)))))

 (=> Check lookup)

 (Check (ctx (prev Nat)
             (motive (-> Nat Type))
             (base (motive zero))
             (step (Pi ((prev Nat))
                     (-> (motive prev)
                         (motive (add1 prev))))))
   prev Nat)

 (=> Check lookup)

 (Check (ctx (prev Nat)
             (motive (-> Nat Type))
             (base (motive zero))
             (step (Pi ((prev Nat))
                     (-> (motive prev)
                         (motive (add1 prev))))))
   (prev motive base step)
   Nat)

 (=> omitted))
```

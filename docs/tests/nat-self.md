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
    (Pi ((motive (Pi ((target Nat)) Type))
         (base (motive zero))
         (step (Pi ((prev Nat)
                    (almost (motive prev)))
                 (motive (add1 prev)))))
      (motive target))))
```

Compare the definition of `Nat` to the type of `ind-Nat`.

```scheme
(claim ind-Nat
  (Pi ((target Nat)
       (motive (Pi ((target Nat)) Type))
       (base (motive zero))
       (step (Pi ((prev Nat)
                  (almost (motive prev)))
               (motive (add1 prev)))))
    (motive target)))
```

We get `Nat` by making the target of `ind-Nat`'s type the **self type**.

- This trick of shifting one argument,
  is just like the trick between `factorial` and `factorial-wrap`.

This is derivable from the definition of `ind-Nat`,
which just apply the `target` to the reset of the arguments.

```scheme
(define (ind-Nat target motive base step)
  (target motive base step))
```

- The story goes like this:

  We know `ind-Nat`'s type.
  It is an expression of mathematical induction.

  How to implement it's function body?
  There are infinitely many ways to do this.
  Let's choose the most simple definition
  that takes into account all the information available,
  namely `(target motive base step)`.

  We get lambda encoding in this way.

  And we can try to solve `Nat`,
  i.e. to find a definition of `Nat`
  that works with `ind-Nat`'s definition.

  And we invent self type.

Note that, in the defining of `Nat`,
`zero` and `add1` occurred,
but the type of `zero` is `Nat`.

And `Nat` also occurred in the defining of `Nat`,
but this does not require us to have a `Nat` to build a `Nat`
(If so, we won't be able to build the first `Nat`),
instead if require us to have functions
which take `Nat` as argument to build a `Nat`.

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

# The Notion of Contradiction

## Absurd

```scheme
(define Absurd (Pi ((A Type)) A))

(claim from-falsehood-anything
  (Pi ((target Absurd)
       (motive Type))
    motive))

(define (from-falsehood-anything target motive)
  (target motive))
```

## Equal (Leibniz)

```scheme
(claim Equal
  (Pi ((A Type)
       (from A)
       (to A))
    Type))

(define (Equal A from to)
  (Pi ((motive (-> A Type))
       (base (motive from)))
    (motive to)))

(claim same
  (Pi ((A Type) (a A))
    (Equal A a a)))

(define (same A a)
  (lambda (motive base) base))

(claim replace
  (Pi/implicit ((A Type) (from A) (to A))
    (Pi ((target (Equal A from to))
         (motive (-> A Type))
         (base (motive from)))
      (motive to))))

(define replace
  (lambda/implicit (A from to)
    (lambda (target motive base)
      (target base))))
```

Fu Peng proposes to use the following `Absurd`.

```scheme
(define Absurd
  (Pi ((A Type) (from A) (to A))
    (Equal A from to)))

(claim from-falsehood-anything-equals
  (Pi ((target Absurd)
       (A Type)
       (from A)
       (to A))
    (Equal A from to)))

(define (from-falsehood-anything-equals target A from to)
  (target A from to))
```

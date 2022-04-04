---
title: Typing Encoding of Natural Number with Self Types
---

Remember that `ind-Nat` take `target` as an explicit argument,
because we want to infer application of `ind-Nat`.

```scheme
(claim ind-Nat
  (Pi ((target Nat)
       (motive (-> Nat Type))
       (base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive target)))

(define (ind-Nat target motive base step) (target motive base step))
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

Here comes **self types**.

```scheme
(define Nat
  (Self (target)
    (Pi ((motive (-> Nat Type))
         (base (motive zero))
         (step (Pi ((prev Nat))
                 (-> (motive prev)
                     (motive (add1 prev))))))
      (motive target))))
```

The following type checking must pass

```scheme
(check (ctx)
  zero
  (Self (target)
    (Pi ((motive (-> Nat Type))
         (base (motive zero))
         (step (Pi ((prev Nat))
                 (-> (motive prev)
                     (motive (add1 prev))))))
      (motive target)))
  (Pi ((motive (-> Nat Type))
       (base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive zero)))

(check (ctx)
  add1 (-> Nat Nat))

(check (ctx)
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

(check (ctx (prev Nat))
  (lambda (motive base step)
    (step prev (prev motive base step)))
  (Self (target)
    (Pi ((motive (-> Nat Type))
         (base (motive zero))
         (step (Pi ((prev Nat))
                 (-> (motive prev)
                     (motive (add1 prev))))))
      (motive target))))

(check (ctx (prev Nat)
            ((self target)
             (lambda (motive base step)
               (step prev (prev motive base step)))))
  (lambda (motive base step)
    (step prev (prev motive base step)))
  (Pi ((motive (-> Nat Type))
       (base (motive zero))
       (step (Pi ((prev Nat))
               (-> (motive prev)
                   (motive (add1 prev))))))
    (motive target)))

(check (ctx (prev Nat)
            ((self target)
             (lambda (motive base step)
               (step prev (prev motive base step))))
            (motive (-> Nat Type))
            (base (motive zero))
            (step (Pi ((prev Nat))
                    (-> (motive prev)
                        (motive (add1 prev))))))
  (step prev (prev motive base step))
  (motive target))
```

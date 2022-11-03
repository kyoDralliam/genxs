GenXS
======

Metaprogramming exercises in MetaCoq

Requirements
--------------

- Coq 8.16
- MetaCoq 1.1.1


Contents
----------

- Discriminators and projectors generation for inductive types
  e.g.
      `MetaCoq Run (gen_projectors "option"%bs)` generates
  ```
      isNone : option A -> bool,
      isSome : option A -> bool,
      projSome_0 : forall (o : option A), isSome o -> A
  ```
  (in theories/genDiscriminators.v)

- A proof of well-typedness of discriminators (pcuic version) stating
  that for any declared inductive I in a well-formed environnement Σ containing 𝔹,
  and constructor C of I with corresponding discriminator is_c obtained through
  the function generating discriminators
  Σ ⊢ isC : ∀ params indices, I params indices → 𝔹

- Typeclass based Eta-laws for inductive/positive records

  (in theories/etaRecord.v)

- A tentative to unbundle records (theories/unbundling.v and theories/quoteRecord.v)


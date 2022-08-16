GenXS
======

Metaprogramming exercises in MetaCoq

Requirements
--------------

- Coq 8.15
- MetaCoq 1.0 (the template part at least, as provided by coq-metacoq-template.1.0+8.15 on opam)


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
  
  
- Typeclass based Eta-laws for inductive/positive records
  
  (in theories/etaRecord.v)

- A tentative to unbundle records (theories/unbundling.v and theories/quoteRecord.v)
  

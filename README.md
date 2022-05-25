NOTE: Work is primarily done on this fork https://github.com/vcvpaiva/Dialectica

# Dialectica

2022 AMS MRC on Applied Category Theory

1. basic categories

2. DialSet.agda = chapters 1 and 2 of https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf over Set.

This exists in two different kinds: 

A. objects as subsets of U \times X  (we want to have the code, but will not do much with it to begin with) OR

B. objects as maps into Two, U\times X--> Two, which we will work on to begin with (thinking of L, but workign with Two)

These two kinds are equivalent in the category Set.

(later DialC, C any finite limit, CCC cat)

3. LDialSet.agda = chapters 3 and 4 of https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf, over Set.
Note the simplified morphisms, but much more complicated tensor products.
(later LDialC, C any finite limit, CCC cat)

4. Lineales = poset reflection of an smcc (symmetric monoidal closed category)
(to begin with Two, later Three, Four, Q, Z, R, [0,1])

5. \*-autonomous posets = Girard algebras (possibly)= poset reflection of \*-autonomous categories, full duality

6. Petri nets: Using two copies of DialSet and two relations pre, post: U\times X --> L or in the new notation pre, post: pos A\times dir A --> Two

7. Event structures (possibly, to make connection to Dialectica games, Winskel)

8. Poly = chapters  1,2, ... Not all, but following Nelson's suggestion we should do Dynamical Systems.



# References

Dialectica Petri Nets https://arxiv.org/abs/2105.12801, Elena's slides

Lineales https://drive.google.com/file/d/1Xk-2LKABGNfnYTf9CGV6lkhWBUHpGT9m/view?usp=sharing

Winskel's Dialectica games in https://arxiv.org/pdf/2202.13910.pdf, video https://www.youtube.com/watch?v=ywHNG6DYAGg, slides 


## Sources
https://github.com/heades/cut-fill-agda
reimplementing in Cubical Agda

https://github.com/heades/dialectica-spaces/tree/master


# Universes in Lean

Some Lean files to support a seminar talk on the use of universes in
mathematics. Key exhibit is a "greedy" construction of the Stone-Cech compactification of
a topological space `X` which proceeds by taking the product `\Prod Y` ranging
over all continuous maps `X -> Y` with `Y` compact and Hausdorff. The Stone-Cech
compactification
is then the closure of the image of `X` in this product.

The issue now is that this construction will live at a higher universe level. To
conclude, one shows that the closure of a "small" subset of a "big" Hausdorff
space is small.

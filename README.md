pymath
======

Python code for mathematical classes

Classes to implement finite fields (ffield.py), rationals and complex rationals (rational.py),
quaternions (quaternion.py), matrices (matrix.py) over any ring, and
single-variable polynomials and rational functions (poly.py) with coefficients in any field.
Also, a class to implement undirected graphs (graph.py).

Test programs for the various classes are included:
test_ffield.py primarily tests ffield.py, but also uses matrix.py and poly.py
test_matrix.py primarily tests matrix.py, but also uses poly.py and rational.py
test_poly.py primarliy tests poly.py, but also uses ffield.py and rational.py

A demonstration of secret sharing using finite fields is also included (share.py),
together with an html-based slide presentation (secretsharing.html)

A demonstration of using the classes to create binary BCH codes is also included (bch.py)

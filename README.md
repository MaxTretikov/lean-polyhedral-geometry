# lean-polyhedral-geometry

Lean formalization of basic polyhedral-geometry constructions used by the
LP feasibility proofs, including:
- cones and conical hulls
- orthant and hyperplane intersections
- generator sets and face representations
- interior-point and Farkas-combination lemmas

This library provides the geometric substrate for the cone-construction
algorithm formalized in `ninth/proof`, and is intentionally scoped to the
definitions and lemmas needed by that development.

# Search results for q = 7, 11, 19, 23, 27, 31

Each file `q_<q>.txt` is the unedited output of `../search/bsw_search.c` (rebuild with
`sh ../search/make_data.sh`). It lists **all** complete exterior sets of the conic that contain the
point {0, ∞} and are not linear.

A line such as

```
NON-ELLIPTIC psi: {1,3} {2,6} {4,5}
```

describes one set: the point {0, ∞} together with the pairs {1, 3}, {2, 6}, {4, 5}, in the language of
Section 3 of the paper. The linear sets (ψ(x) = n/x, one for each non-square n) are only counted, not
listed. The last two lines are statistics of the search: the numbers of solutions
(`solutions = elliptic + non_elliptic`, "elliptic" meaning linear), the size of the search tree and the
running time.

Field elements are written as integers. For prime q this is the usual residue. For q = 27 the integer
a₀ + 3a₁ + 9a₂ stands for a₀ + a₁u + a₂u², where u³ + 2u + 1 = 0 over F₃.

| q | linear sets | other sets | of them with no three collinear points |
|---|---|---|---|
| 7 | 3 | 2 | 2 |
| 11 | 5 | 7 | 2 |
| 19 | 9 | 45 | 0 |
| 23 | 11 | 110 | 0 |
| 27 | 13 | 91 | 0 |
| 31 | 15 | 16 | 0 |

The last column is computed by `../checks.py`.

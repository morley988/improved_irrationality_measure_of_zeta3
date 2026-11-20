# Cubic second-layer arithmetic: independent audit

Research checkpoint, 19 November 2026. This note audits the arithmetic used in
the current Pearson determinant investigation for the irrationality measure
of zeta(3). It establishes the local valuation formulas and their limiting
profiles. It does **not** certify the final numerical integral or claim an
improved irrationality-measure bound.

The underlying project proofs are in `zeta5_spectral_transfer.tex`, section
“The general second local layer”, and `zeta5_journal_publication.tex`, sections
“Monomial residues, quotient support, and mixed minors”, “The common-root
gain”, and the small-prime lemma. The arguments below explain the changes
needed for the cubic functional and allow two different factorial windows.

## 1. Setup and the cubic functional

Let

\[
 P_j(x)=\frac{\prod_{a=0}^{j-1}(x^2-a^2)}{(2j)!},\qquad
 b_j(t)=\frac{(-1)^j\prod_{a=0}^{j-1}(t+a^2)}{(2j)!},\qquad
 D_N(t)=\prod_{i=1}^N(t+i^2).
\]

Thus `P_j(x)=b_j(-x^2)`. At odd primes these polynomials form the
triangular basis of the even integer-valued lattice used in the project.
For positive integers `m_1,m_2,r`, put `R_i=m_i+r` and

\[
 A_{jk}(X)=(N!)^2\mathcal J_{3,X}
   \left(\frac{b_{m_1+j}(t)b_{m_2+k}(t)}{D_N(t)}\right),
 \qquad 0\le j,k<r.
\]

The identities needed in the audit are

\[
 \mathcal J_{3,X}\left(\frac1{t+i^2}\right)
 =i^2X-i^2H_{i-1}^{(3)}-\frac1{2i}-\frac12,
 \qquad
 \mathcal J_{3,X}(q(t))=\frac12\mathcal B\frac d{dx}
       [x^3q(-x^2)],
\]

where `B(x^j)=B_j` with `B_1=-1/2`. In particular the rational moments are

\[
 \mathcal J_{3,X}(t^k)=\frac{(-1)^k(2k+3)B_{2k+2}}2.
\]

Use the good-prime hypotheses

\[
 p>5,\qquad p^2>4\max(R_1,R_2)+20,\qquad p^2>2N+20.
\]

For the local layers assume `p<=N`, write `N=qp+sigma`, and put
`epsilon=floor(2 sigma/p)`, `n=(p-1)/2`, `h=2q+1+epsilon`.
The maximal reflected classes `M` have `h` physical nodes and the other
classes `T` have `h-1` nodes:

| epsilon | M | T | w=card(M) |
|---|---|---|---|
| 0 | 1,...,sigma | sigma+1,...,n | sigma |
| 1 | p-sigma,...,n | 1,...,p-sigma-1 | sigma-n |

The signed levels of a class are
`K_c={a in Z: 1<=abs(c+pa)<=N}`. On `T` these are `-q,...,q-1`
if epsilon is zero and `-q,...,q` if epsilon is one.

## 2. Bernoulli precision after one derivative

The general Newton estimate remains unchanged. If `g` is integer-valued
at `p`, `deg(g)=L<p^2`, and `E=floor(L/p)`, then

\[
 v_p([Y^j]g(c+pY))\ge\max(0,j-E).
\]

For the cubic application a particularly simple sufficient precision
condition is `E<=p-3`. Under that condition, local reduction modulo `p`
or `p^2` can precede one derivative and Bernoulli evaluation. For a term
of degree `j<p`, `B_{j-1}` is integral. For `j>=p`, its coefficient has
valuation at least three; the possible loss of one Bernoulli denominator
still leaves valuation at least two. The same argument proves the
modulo-p version.

This sufficient condition holds automatically for the actual quotient.
If `f,g` lie in the two windows and `I` is their factorial-basis truncation
through index `N`, define

\[
 Q_{fg}(x)=(N!)^2\frac{f(x)g(x)-I(x)}{D_N(-x^2)}.
\]

Its relevant Bernoulli input has degree

\[
 \deg(x^3Q_{fg})\le 2R_1+2R_2-2N-1
 \le4R_{\max}-2N-1.
\]

Because `N>=p` and `p^2>4R_max+20`, its local degree bound is at
most `p-3`. Multiplication by the powers of `p` below does not change
this degree, and integer-valuedness follows from the local quotient
factorization.

There is no counterexample to the conversion hidden here. In fact the
broader `E<=p-1` condition can also be treated: the first potential
Bernoulli pole, at `j=p`, is canceled by the derivative factor `j=p`.
The stronger automatically available `E<=p-3` condition avoids needing
that refinement. A proof copied literally from the three-derivative
case should nevertheless replace its degree discussion explicitly.

## 3. The cubic universal local functional and parity

For `K={-q-eta,...,q}`, `eta` zero or one, let
`L(Y)=product_{a in K}(Y-a)`, and let `I_P` be the remainder of `P`
modulo `L`. Define

\[
 H_3(a)=\begin{cases}
   \sum_{j=1}^a j^{-3},&a\ge0,\\
   \sum_{j=1}^{-a-1}j^{-3},&a\le-1,
 \end{cases}
\]

\[
 \mathcal T_{q,\eta}^{(3)}(P)
 =\sum_{a\in K}\frac{H_3(a)P(a)}{L'(a)}
   +\frac12\mathcal B\left[
       \left(\frac{P-I_P}{L}\right)'\right].
\]

For `eta=1`, reflection `S(Y)=-1-Y` preserves `K`, preserves `L`,
and preserves `H_3`; `L'` changes sign. The quotient derivative also
changes sign, while `B(F(-1-Y))=B(F(Y))`. Consequently

\[
 \mathcal T_{q,1}^{(3)}(P\circ S)
 =-\mathcal T_{q,1}^{(3)}(P).
\]

Thus the same two-parity rank bound is available as in the quintic
argument. There is no change of parity caused by replacing three
derivatives with one.

## 4. Complete features and the second determinant layer

For side `i=1,2`, set

\[
 D_i=\left\lfloor\frac{2R_i-2}{p}\right\rfloor,
 \quad J_i=\lceil D_ip/2\rceil,\quad H_i=R_i-J_i,
 \quad k_i(c)=\#\{a:|c+pa|<m_i\}.
\]

Assume `m_i<=J_i` when using the following exact feature description.
The low space on a nonzero class is
`Z_{k_i(c)} F_p[Y]_{<=D_i-1-k_i(c)}`, where

\[
 Z_{2a}=\prod_{v=-a}^{a-1}(Y-v),\qquad
 Z_{2a+1}=\prod_{v=-a}^{a}(Y-v).
\]

The full low-feature dimension is `J_i`; this follows from the local
Newton bound and injectivity on integer evaluations. The `m_i` initial
evaluation conditions are independent, so the root constraints are
independent across classes. Top coefficients are polynomials of degrees
`0,...,H_i-1` in `c^2`, with a common extra factor `c` in the odd band.
Evaluation at the `w` distinct nonzero squared nodes therefore has rank
`min(H_i,w)`. These are lattice facts, independent of the zeta exponent.

Put

\[
 L_i=\sum_{c\in M}(D_i-k_i(c))_+,
 \quad A_i=L_i+\min(H_i,w),\quad K_i=(H_i-w)_+.
\]

The restriction to `M` has exact rank `A_i`; its kernel has `K_i`
remaining top-coefficient directions.

The leading cubic matrix is `p^{3+epsilon}A mod p`. It factors through
the maximal restriction maps. On a nonzero class, write

\[
 D_N(-(c+pY)^2)=p^{h_c}L_c(Y)U_c(Y),
\]

where `U_c mod p` is a constant unit. The leading functional has
nonzero multiplier

\[
 \omega_c=2c^3\frac{(N!/p^q)^2}{\overline U_c}.
\]

The coefficient of `X` in `A` has valuation at least `-epsilon`, so
both local layers are constant in `X`.

On both maximal restriction kernels the next reduction is

\[
 p^{2+\epsilon}A\pmod p
   =\text{pullback of }
     \bigoplus_{c\in T}\omega_c\mathcal T_*^{(3)},
\]

where `T_*` is `T_{q-1,1}` for epsilon zero and `T_{q,0}` for
epsilon one. The quotient check is as follows.

On `M`, both local input polynomials are zero modulo `p`, so their
product is divisible by `p^2`. The reduction of `I` has degree at most
`h-1` and vanishes at `h` physical nodes; therefore it is zero.
The next reduction `I/p` has degree at most `h` and is a multiple
of `L_c`. It follows that `p^epsilon Q_fg` is integral and constant
modulo `p` on `M`.

On `T`, the reduction of `I` differs from interpolation remainder
by a constant multiple of `L_c`. Distribution gives the exact identity

\[
 p^{2+\epsilon}\operatorname{Quot}(f,g)
 =\frac12\sum_{c=0}^{p-1}\mathcal B_Y\partial_Y
    [(c+pY)^3p^\epsilon Q_{fg}(c+pY)].
\]

The preceding precision argument allows reduction before the derivative.
The maximal and interpolation constants disappear: differentiating the
remaining `(c+pY)^3` supplies a factor `p`. On the zero class,
`Q_fg(pY)` is integral and the factor `(pY)^3` makes the contribution
zero even allowing one Bernoulli denominator. Proper fractions on `M`
gain `p^2` from the two kernel conditions and vanish at this scale;
those on `T` give the residue term in `T_*`. Physical multiples of `p`
and the retained constant quotient from `P_N` also vanish at this scale.

Let `B` be a rank bound for this second pullback. Constant unimodular
changes of basis adapted to the two kernels yield

\[
 \boxed{\ v_p\det A(X)\ge
       -(1+\epsilon)r-A_1-A_2-B.\ }
\]

Indeed, for `M_0=p^{3+epsilon}A`, every kernel row and column is
divisible by `p`. The common kernel block after division by `p` has
rank at most `B`, so determinant factorization gives
`v_p(det M_0)>=2r-A_1-A_2-B`. This remains valid when the indicated
number of extra rows is negative, by the weaker single-side factorization.

For `u_i` zero or one, put `n_i=(D_i+u_i-k_i(c))_+`. A valid local
rank cap is `min(n_1,n_2)`. If epsilon is zero and both `k_i(c)` are
even, anti-invariance improves it to

\[
 \min(\lceil n_1/2\rceil,\lfloor n_2/2\rfloor)
 +\min(\lfloor n_1/2\rfloor,\lceil n_2/2\rceil).
\]

Thus all four numbers

\[
 B_{u_1,u_2}=\sum_{c\in T}b_c(u_1,u_2)
       +(1-u_1)K_1+(1-u_2)K_2
\]

are upper bounds for `B`. Also cap by `r-A_1` and `r-A_2`.
These formulas are valid for different windows without any extra
symmetry assumption.

## 5. Cubic monomial profile, including unequal windows

An exact change of basis gives

\[
 \det A=\frac{(N!)^{2r}}
  {\prod_{j=m_1}^{R_1-1}(2j)!\prod_{k=m_2}^{R_2-1}(2k)!}
  \det H,
 \quad H_{jk}=\mathcal J_{3,X}
     (C_{m_1}C_{m_2}t^{j+k}/D_N),
\]

up to an irrelevant sign. Here `C_m(t)` is the monic common-root
polynomial. The residue atoms have rank one and the quotient is
an integer-coefficient polynomial evaluated by the rational moments.

The first possible Bernoulli pole occurs at `2k+2=p-1`, and its
denominator is canceled by `2k+3=p`. The first uncanceled possible
moment index is `k=p-2`. All needed moments have valuation at least
`-1`. It follows that the fractional part of the quotient matrix is
supported in a terminal square block of size

\[
 t_p=\min\{r,(R_1+R_2-N-p+1)_+\}.
\]

Every quotient minor of order `a` therefore costs at most `min(a,t_p)`.

Assume

\[
 N/3<p\le N,\qquad p>2\max(m_1,m_2),\qquad r\ge H_p,
 \quad H_p=N-p-(q-1).
\]

In a nonzero reflected class with two low nodes and `h` high nodes,
selecting `ell` atoms, of which `b` are high, costs at most

\[
 3b+\ell(h+2-\ell).
\]

This uses harmonic loss three, derivative-denominator loss `h+1`
per atom, and the two Vandermonde minors' recovery `ell(ell-1)`.
For `1<=h<=4` its maximum is `5h`; if `ell=h-d<h`, its deficit
from this maximum is `d(5-h)+d^2>=d`. Selections above `h` do not
exceed `5h`. Unaffected all-low pairs are integral because
`H_{p-i-1}^{(3)}=H_i^{(3)} mod p` gives the usual paired-residue
cancellation.

For `p>N/2`, one has `h<=2`. If precisely `a` of the two window
common factors have a root in the class, `a` is 0, 1, or 2. Every
surviving atom gains `a` powers of `p`; the low node at that root
vanishes. The maximum cost becomes `(5-a)h`, and the deficit for
`ell=h-d<h` is `d(5-a-h)+d^2>=d`. Thus each common factor contributes
its own one-power saving per affected high node.

For `N/3<p<N/2`, the implementation deliberately discards all these
common-root savings. This is a useful validity guard: if `h=4` and
`a=2`, the cubic affected-class cost at `ell=3` equals its cost at
`ell=4`. The one-power deficit needed for sharing the quotient
dimension would then fail. Using the unaffected `5h` bound avoids
this issue completely.

The zero class is integral because `m_1,m_2>=1`. Each common factor
has valuation two at `i=ap`, the cubic scalar functional costs at
most one, and the derivative denominator costs `2(q-1)`. Each such
atom has valuation at least `5-2q>=1` for `q<=2`.

Summing class maxima, their one-power deficits, and the complementary
quotient minor gives, for the upper band `p>N/2`,

\[
 v_p(\det H)\ge-5H_p+A_{m_1}(p)+A_{m_2}(p)
                      -\min(t_p,r-H_p),
\]

where `A_m(p)=min(m-1,sigma)+(m-p+sigma)_+` when `q=1`.
For `N/3<p<N/2` use the same formula with both `A` terms set to zero.

Take `m_i/N -> s_i>0`, `r/N -> delta`, `rho_i=s_i+delta`, and
`beta=p/N`. Put `q=floor(1/beta)` and `D_i=floor(2rho_i/beta)`.
Under `beta>max(1/3,2max(s_i))`, the factorial cost is

\[
 f(\beta)=\sum_{i=1}^2\left(D_i\rho_i-
                      \frac{\beta D_i(D_i+1)}4\right)-2\delta q.
\]

Define

\[
 a_i(\beta)=\begin{cases}
 0,&\beta<1/2,\\
 \min(s_i,1-\beta)+(1+s_i-2\beta)_+,&\beta>1/2.
 \end{cases}
\]

A valid limiting clearing-cost profile, provided `delta>=1-beta`, is

\[
 \boxed{ f(\beta)+5(1-\beta)-a_1(\beta)-a_2(\beta)
       +\min\{(\rho_1+\rho_2-1-\beta)_+,\delta-1+\beta\}. }
\]

For `beta>1`, all residue atoms or reflected pairs are integral, but
the cubic quotient need not be integral. The valid profile is

\[
 \boxed{f(\beta)+(\rho_1+\rho_2-1-\beta)_+.}
\]

The latter uncapped terminal cost is conservative. For the parameters
currently investigated, `s_i<1/2`, so its factorial expression applies
throughout `beta>1`. For a completely general window with `s_i>=1/2`,
the lower-end factorial terms must be restored.

## 6. Small primes and the tail 4 delta / Q

The first-layer cubic bound is

\[
 v_p\det A\ge-(2+\epsilon)r
       -\min\{r,(\min(D_1,D_2)+1)w\}.
\]

Consequently its normalized cost is at most `4 delta` for `0<beta<1`.
This bound is enough to replace the interval `0<beta<1/Q` by
`4 delta/Q`; it does not use a small-prime extrapolation of the
good-prime lemma.

To justify that distinction, first clear all primes `p<=Y=N^(9/10)`
using the uniform bound

\[
 v_p(A_{jk})\ge-9L_p-v_p(96),\qquad
 L_p=\lfloor\log_p(4R_{\max}+4)\rfloor.
\]

The existing proof for the quintic matrix is also an upper bound here.
For proper fractions, the factorial ratio loses at most `L_p`, the
cubic harmonic sum at most `3L_p`, and the integer-valued basis only
fixed powers of two. For the polynomial part the factorial ratio loses
at most `5L_p`; one derivative and Bernoulli evaluation cost at most
two further `L_p`, less than the four allowed by the quintic proof.
The finite constants are also covered by `96`. The same proof works
for unequal windows, using the product-basis expansion through degree
at most `R_1+R_2-2` and the common upper bound `R_max`.

The log cost for clearing these entries and taking an `r` by `r`
determinant is `O(N^(19/10) log N)=o(N^2)`. Every remaining prime is
good for all sufficiently large `N`. For `Y<p<N/Q`, use the bound
`4r`; the prime number theorem gives normalized total at most
`4 delta/Q+o(1)`.

Thus the conservative tail used by the numerical code is justified.
All fixed finite exceptional primes, exact endpoint primes, and
integer rounding offsets are harmless after this initial clearance.
The limiting profiles should be integrated first with a fixed `Q`,
and only then may `Q` increase.

## 7. Audit conclusions and limits

The cubic second-layer exponent, the parity improvement, asymmetric
feature dimensions, the monomial profile in both prime ranges, and
the conservative tail are valid under the explicit guards above.
No arithmetic defect was found in `second_layer.py` or the arithmetic
part of `asymmetric_probe.py` as examined on 19 November.

Four-point Gauss integration across a panel containing competing
affine branches is not an exact certificate. The profile is piecewise
affine, but every floor breakpoint and every intersection at which a
min/max changes branch must be respected, or an independent certified
enclosure used. An exact rational cellwise implementation is being
prepared separately. No final record claim should be made until that
arithmetic certificate, the analytic response certificate, and the
root-multiplicity transfer assumptions have all been checked together.

For comparison, the existing CMF certificate already implies about
`5.419648258155345`; simply replacing the published rounded headline
`5.4197` with more digits is not an improvement.

## 8. Exact arithmetic certificate subsequently reviewed

For the rational parameters

\[
 (s_1,s_2,\delta)=\left(\frac2{25},\frac8{25},\frac{51}{50}\right),
 \qquad Q=500,
\]

the independently reviewed `exact_arithmetic.py` implementation gives

\[
 C_{\rm ar}\le
 \frac{1926282169226183949}{500000000000000000}
 =3.852564338452367898.
\]

This includes the conservative tail `51/6250`. The finite integral is
bounded by `1922202169226183949/500000000000000000`. The implementation
enumerates the breakpoints of `floor(1/beta)`, `floor(2/beta)`,
`floor(2rho_i/beta)`, and `floor(s_i/beta)`, and dynamically splits
each min/max or ordering comparison at its exact rational intersection.
It uses rational affine functions throughout. Every accepted cell's
area is rounded upward to a multiple of `10^-18`; the entire rounding
allowance is less than `6.752e-15`.

An independent read of the full cell file checked all 6,752 cells:
their union is the contiguous interval `[1/500,67/25]`, every upward
area rounding is valid, and the summed finite integral, tail, and
metadata agree. The cell file has SHA256

`fcfa9c5d70e7f54d40c74296354a97b82b4a04b5be7db9afaa06ebe09878d049`.

As an additional diagnostic comparison, 150 sampled cells at three
interior points each agreed with the separately implemented floating
profile to within `1.34e-13`. That floating comparison is not needed
for the exact bound. The certificate is the rational integration and
the audited local valuation inequalities.

The analytic response and final irrationality-measure comparison still
require their separate certificates; this section certifies only the
arithmetic input.

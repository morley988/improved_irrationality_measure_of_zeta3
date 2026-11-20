# Cubic Pearson nullity and quantitative transfer

Independent adaptation audit, 19 November 2026. The following gives the
structural input for the two-window cubic determinant. It is independent
of the final numerical analytic certificate.

## Exact cubic Pearson identity

Define a functional on rational functions with polynomial part and simple
integer poles by

\[
 \mathcal K_{3,X}(f)=\frac12\mathcal B(f')\quad(f\in\mathbb C[x]),
 \qquad
 \mathcal K_{3,X}\left(\frac1{x-i}\right)=
 \begin{cases}-X+H_i^{(3)},&i\ge0,\\
              -X+H_{-i-1}^{(3)},&i\le-1.
 \end{cases}
\]

The Bernoulli shift identity and direct verification at each pole give

\[
 \mathcal K_{3,X}(f(x+1)-f(x))=[x^2]f(x),
 \qquad
 \mathcal K_{3,X}(f)=-\tfrac12[x^2]f
       \quad\hbox{if }f\hbox{ is even}.
\]

Moreover,

\[
 \mathcal J_{3,X}(h(t))=\mathcal K_{3,X}(x^3h(-x^2)).
\]

For the simple-pole verification use
`x^3/(i^2-x^2)=-x-i^2 x/(x^2-i^2)`; this gives exactly
`i^2 X-i^2 H_{i-1}^{(3)}-1/(2i)-1/2`.

Assume `1<=m_1<=m_2<=N` and put

\[
 W(x)=x^3\frac{C_{m_1}(-x^2)C_{m_2}(-x^2)}{D_N(-x^2)},
 \qquad \mathcal L_X(f)=\mathcal K_{3,X}(Wf).
\]

The function `W` is odd, has at most simple integer poles, and vanishes
to order seven at zero. Its exact ratio is

\[
 \frac{W(x+1)}{W(x)}=
 \left(\frac{x+1}{x}\right)^6
 \frac{(x+m_1)(x+m_2)(x-N)}
      {(x-m_1+1)(x-m_2+1)(x+N+1)}.
\]

Set

\[
 A(x)=(x-1)^6(x-m_1)(x-m_2)(x+N),\qquad
 B(x)=(x+1)^6(x+m_1)(x+m_2)(x-N).
\]

These are degree-nine monic polynomials, `B(x)=-A(-x)`, and
`W(x+1)A(x+1)=W(x)B(x)`. The vanishing at zero makes the shift
coefficient `[x^2](WAf)` zero. Hence

\[
 \mathcal L_X(B(x)f(x+1)-A(x)f(x))=0.
\]

Also `L_X` vanishes on odd polynomials, by the even-function identity
for `K`. Nothing in these identities uses the quintic functional.

## Nullity at most two

Let

\[
 H_N(X)=\left[\mathcal J_{3,X}
     \left(\frac{C_{m_1}C_{m_2}t^{j+k}}{D_N}\right)
       \right]_{0\le j,k<r}.
\]

Suppose `r>N-m_2+1`. Then `nullity(H_N(X))<=2` for every complex `X`.
Here is the adaptation of the project's polynomial-adjoint proof.

The finite Hankel kernel lemma says that if the nullity is `m>0`,
its least-degree monic kernel polynomial `p` of degree `j` satisfies
`j<=r-m`, has nonsingular leading Hankel matrix of size `j`, and is
orthogonal through degree `M=r+m-2`. Define `P(x)=p(-x^2)` and

\[
 \mathcal Df=B(x)(f(x+1)-f(x))
        -B(-x)(f(x-1)-f(x)),
 \quad \mathcal Qf=\operatorname{even}[B(x)f(x+1)],
 \quad \mathcal Rf=x\mathcal Df.
\]

Pearson gives self-adjointness of `D`, and on even polynomials the
adjoints of `Q,R` are

\[
 \mathcal Q^*g=\operatorname{even}[A(x)g(x-1)],
 \qquad \mathcal R^*g=\mathcal D(xg).
\]

Because `B` is monic of odd degree nine, the possible degree gain
eight in `D` cancels. Thus `D` has degree gain at most seven.
Each of `Q,Q*,R,R*` preserves evenness and has degree gain at most
eight in `x`, hence at most four in `t=-x^2`.

If `m>=3`,

\[
 j+3\le r-m+3\le r+m-2=M.
\]

The polynomial-adjoint remainder lemma consequently gives
`P | QP` and `P | RP`. At any nonzero root `alpha` of `P`, their
sum and difference force

\[
 B(\alpha)P(\alpha+1)=0.
\]

All roots of `B` are integers. A noninteger root of `P` therefore
propagates indefinitely under addition of one, a contradiction.
Every root of `P` is an integer; all roots of the monic `p(t)` are
nonpositive squares. In particular `p(t)>0` for `t>0`, even though
the initial functional and kernel were allowed to be complex.

The pole-clearing polynomial

\[
 E(t)=\prod_{i=m_2}^N(t+i^2)
\]

has degree less than `r`. The kernel condition gives `L_X(pE)=0`.
Exact cancellation instead gives

\[
 L_X(pE)=\mathcal J_{3,X}(p(t)tC_{m_1}(t))
       =\int_0^\infty p(t)tC_{m_1}(t)\,d\mu_3(t)>0,
\]

because the polynomial moments are independent of `X` and the cubic
measure is strictly positive:

\[
 d\mu_3(x^2)=4\pi^2 x^3
      \sum_{k\ge1}k^2 e^{-2\pi kx}\,dx,\qquad x>0.
\]

This contradiction proves the nullity bound.

At `xi=zeta(3)`, `G_N=H_N(xi)` is positive definite. The relative
pencil is `I+(X-xi)T_N` with real symmetric
`T_N=G_N^(-1/2) M_N G_N^(-1/2)`, where `M_N=[X]H_N`.
Real symmetric diagonalization makes the multiplicity of each finite
determinant zero equal to the matrix nullity there. Thus all finite
zeros of the primitive integer determinant polynomial have multiplicity
at most two. Constant changes of basis and scalar normalization do not
change this assertion.

## Degree for the proposed rational parameters

The slope matrix is a sum of the nonzero residue atoms at
`t=-i^2`, `m_2<=i<=N`. Their weights are nonzero. If
`r>=N-m_2+1`, the rectangular evaluation matrix has full column rank,
so the slope matrix has rank exactly `N-m_2+1`. Symmetric congruence
then shows that this is the determinant degree.

For `N` a positive multiple of 50, take

\[
 m_1=\frac2{25}N,\qquad m_2=\frac8{25}N,
 \qquad r=\frac{51}{50}N.
\]

The nullity hypothesis holds. The exact degree is

\[
 \deg P_N=\frac{17}{25}N+1,
 \qquad \lambda=\frac{17}{25}.
\]

For the target `T=17/125=0.136`, one has `lambda/T=5` exactly.
Also `0<T<delta` and `T<u/2` for the contour parameter under study.

## Contour determinant domination and transfer

The cubic slope has the same polarized residue-contour representation
as the quintic one, with one lower fixed power of the contour variable.
The extra factor is simply `-t` in the sum-of-residues representation:
the cubic pole coefficient is `i^2=-t_i`. This does not affect the
Andreief/triangle-inequality argument.

Choose a real `G_N`-orthonormal basis and let `A_N` be the positive
matrix obtained by replacing the slope's contour measure by its
absolute value and conjugating the second polynomial. For every
principal index set `I`,

\[
 |\det(T_N)_I|\le\det(A_N)_I,
 \qquad
 |\det(I+hT_N)|\le\det(I+|h|A_N).
\]

This controls the determinant response. It does not require an
individual absolute-eigenvalue comparison between `T_N` and `A_N`.
The positive physical measure and the fixed contour prefactor are
valid for the cubic functional; the weighted exponential potential
is unchanged. Fixed polynomial prefactors must still be included in
the norm estimates, but they contribute only subexponential terms
in the existing weighted-polynomial argument.

The quantitative transfer theorem itself is about integer polynomials,
their degree, and their determinant response; it has no dependence on
the zeta order. Suppose

\[
 \deg P_N\le\lambda N+O(1),\qquad
 \log|P_N(\xi)|\le-\varepsilon N^2+o(N^2),
\]

and for some `a>0`, uniformly for each fixed `C>0`,

\[
 \limsup\frac1{N^2}\log
   \sup_{|h|\le Ce^{-aN}}|\det(I+hT_N)|
       \le R(a)<\varepsilon.
\]

Then

\[
 \mu(\xi)\le\frac{\lambda a}{\varepsilon-R(a)}.
\]

To verify the role of multiplicity, let `p/q` be a rational approximation
and let `m<=2` be its multiplicity as a zero of `P_N`, with `m=0`
when it is not a zero. The first nonzero normalized derivative satisfies

\[
 |P_N^{(m)}(p/q)/m!|\ge q^{-(\deg P_N-m)}.
\]

Cauchy on a circle of radius `exp(-aN)` bounds its log size above by
`-(epsilon-R(a))N^2+amN+o(N^2)`. Taking stages
`N~c log q`, with
`lambda/(epsilon-R(a))<c<M/a`, excludes infinitely many approximations
of exponent `M`. Restriction to multiples of 50 changes `N` by only
`O(1)`, so causes no loss. The bounded derivative order costs only
`O(N)`, which is negligible at scale `N^2`.

In the integrated-envelope formulation, a positive decreasing envelope
`g` for the positive contour eigenvalue exponents on `[0,T]`, with
`g(T)>0` and

\[
 \int_0^T g(t)\,dt<\varepsilon,
\]

gives `mu(xi)<lambda/T`. A continuous pointwise envelope need not be
proved decreasing first: its running minimum is an admissible decreasing
envelope and has no larger integral, provided it remains positive.
The certificate must establish the strict integral gap and the required
positive endpoint (or another positive response threshold). The structural
argument alone does not supply those numerical assertions.

For the parameters above, a certified strict response integral at
`T=17/125` would therefore imply `mu(zeta(3))<5`.

## Final transfer arithmetic

The parent investigation subsequently supplied the certified bounds

\[
 \varepsilon-I(T)\ge S=0.004682016878632102,
 \qquad 0<a=g(T)\le a_{\rm up}=6.545408942957.
\]

The final algebra was independently checked with exact rational arithmetic:

\[
 \mu(\zeta(3))\le\frac{\lambda a}{\varepsilon-I(T)+Ta}
 \le\frac{\lambda a_{\rm up}}{S+Ta_{\rm up}}
 =\frac{2225439040605380000}{447428816560392051}
 =4.973839319768086\ldots<4.974.
\]

The direction of the endpoint rounding is correct, since for `S>0`

\[
 \frac{d}{da}\frac{\lambda a}{S+Ta}
   =\frac{\lambda S}{(S+Ta)^2}>0.
\]

This paragraph checks the transfer and exact numerical substitution.
The separate analytic certificate is the source of the displayed
`S` and `a_up` inequalities; it was not reproduced in this note.

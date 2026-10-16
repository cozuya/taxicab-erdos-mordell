# Proof of the taxicab Erdős–Mordell inequality

The proof below includes coordinate ties, boundary medians, and every triangle orientation. The Lean formalization follows the same argument. It proves the strict-interior theorem in [Taxicab/Main.lean](Taxicab/Main.lean) and the boundary estimate in [Taxicab/Basic.lean](Taxicab/Basic.lean).

Let $\Delta$ be the closed triangle with noncollinear vertices $A,B,C$. Use the fixed coordinate distances

$$
d(U,V)=|U_x-V_x|+|U_y-V_y|,\qquad
h(Q;U,V)=\frac{|\det(V-U,Q-U)|}{\max(|V_x-U_x|,|V_y-U_y|)}.
$$

Write

$$
S(Q)=d(Q,A)+d(Q,B)+d(Q,C),\qquad
T(Q)=h(Q;B,C)+h(Q;C,A)+h(Q;A,B).
$$

We prove $3T(Q)\le2S(Q)$ throughout $\Delta$ and prove that the equivalent coefficient $3/2$ is sharp. Noncollinearity makes the endpoints of every side distinct. Thus every denominator in $h$ is strictly positive: a zero maximum of the two nonnegative absolute coordinate differences would force both differences to vanish.

## 1. Endpoint bounds and the boundary

Put $m=\max(|V_x-U_x|,|V_y-U_y|)>0$. The triangle inequality gives

$$
|\det(V-U,Q-U)|
\le |V_x-U_x|\,|Q_y-U_y|+|V_y-U_y|\,|Q_x-U_x|
\le m\,d(Q,U).
$$

Division by $m$ gives $h(Q;U,V)\le d(Q,U)$. Swapping the endpoints gives the second estimate, so

$$
h(Q;U,V)\le\min\{d(Q,U),d(Q,V)\}.
$$

If $Q$ is on the side $BC$, its distance to the supporting line $BC$ is zero. Put $r=d(Q,A)$ and $s=d(Q,B)+d(Q,C)$. The two remaining line distances give both $T(Q)\le2r$ and $T(Q)\le s$. Hence

$$
3T(Q)=T(Q)+2T(Q)\le2r+2s=2S(Q).
$$

Cyclic relabeling proves the estimate on all three sides, including the vertices. In fact, this argument works anywhere on a side's infinite supporting line.

## 2. The coordinatewise median is in the triangle

Let $m_x$ and $m_y$ be the middle values, with repetition allowed, of the three vertex $x$- and $y$-coordinates. Set $M=(m_x,m_y)$.

If a vertex has both median coordinates, then $M$ is that vertex and already belongs to $\Delta$. Otherwise choose $A$ whose $y$-coordinate is $m_y$ and $B$ whose $x$-coordinate is $m_x$. They are distinct. Translate $M$ to the origin. Neither remaining coordinate of $A$ or $B$ is zero, because that would make $M$ a vertex. Reflect the coordinate axes if necessary to put these vertices at

$$
A=(a,0),\qquad B=(0,b),\qquad a,b>0.
$$

Since zero is a median in each coordinate, the third vertex is

$$
C=(-c,-d),\qquad c,d\ge0.
$$

These non-strict inequalities include all coordinate ties. With $D=ab+ad+bc>0$,

$$
(0,0)=\frac{bc}{D}A+\frac{ad}{D}B+\frac{ab}{D}C.
$$

The three coefficients are nonnegative and sum to one, proving $M\in\Delta$. If $c=0$ or $d=0$, a coefficient may be zero and the median may lie on an edge. No interior-median assumption is needed.

Only translations, coordinate reflections, and relabeling have been used. These preserve the given distances. In Lean, inclusive coordinate betweenness and absolute-value identities handle the signs directly; all nine possible sources of the two median coordinates are covered in [Taxicab/Median.lean](Taxicab/Median.lean).

## 3. Distance sums and interpolation

Let $W$ and $H$ be the horizontal and vertical spans of the vertices. For real $u\le v\le w$ and $u\le x\le w$,

$$
|x-u|+|x-v|+|x-w|=w-u+|x-v|.
$$

This remains true with ties. Apply it to each coordinate of any point $Q$ in the triangle, whose coordinates lie in the respective spans. Because $M\in\Delta$, it yields

$$
S(Q)=W+H+d(Q,M)=S(M)+d(Q,M).
$$

For nonnegative weights $\alpha+\beta+\gamma=1$ and $Q=\alpha A+\beta B+\gamma C$, the signed determinant identity

$$
\det(C-B,Q-B)=\alpha\det(B-A,C-A)
$$

and its cyclic versions give

$$
T(Q)=|\det(B-A,C-A)|
\left(\frac{\alpha}{m_{BC}}+\frac{\beta}{m_{CA}}+\frac{\gamma}{m_{AB}}\right),
\qquad m_{UV}=\max(|V_x-U_x|,|V_y-U_y|)>0.
$$

Thus $T$ is affine on the triangle: each determinant has a fixed sign there.

It remains to reduce an arbitrary strictly interior $Q$ to the median and boundary, including the case that the median lies on an edge. Let $p_1,p_2,p_3>0$ be the weights of $Q$ and $\mu_1,\mu_2,\mu_3\ge0$ be weights of $M$, with each triple summing to one. Choose $j$ maximizing $\mu_j/p_j$. Since

$$
\sum_i p_i\frac{\mu_i}{p_i}=1,
$$

this maximum is at least one. If it equals one, all three ratios equal one and $Q=M$. Otherwise $\mu_j>p_j>0$; set

$$
\lambda=\frac{p_j}{\mu_j}\in(0,1),\qquad
r_i=\frac{p_i-\lambda\mu_i}{1-\lambda}.
$$

Maximality gives $r_i\ge0$. Also $\sum_i r_i=1$ and $r_j=0$. Therefore $R=\sum_i r_i V_i$ is on the boundary and $Q=\lambda M+(1-\lambda)R$.

Homogeneity of absolute values and the distance-sum identity now give

$$
S(Q)=\lambda S(M)+(1-\lambda)S(R),\qquad
T(Q)=\lambda T(M)+(1-\lambda)T(R).
$$

Consequently the already proved boundary inequality and the inequality at $M$ imply the inequality at $Q$. This explicit construction is formalized in [Taxicab/Radial.lean](Taxicab/Radial.lean). A point on the closed triangle with a zero barycentric weight was already covered by the boundary argument.

## 4. The median inequality in every orientation

If $M$ is a vertex, the boundary proof applies. Otherwise use the normal form from Section 2:

$$
M=(0,0),\quad A=(a,0),\quad B=(0,b),\quad C=(-c,-d),
\qquad a,b>0,\ c,d\ge0.
$$

Direct evaluation gives

$$
S(M)=a+b+c+d,
$$

$$
T(M)=\min(a,b)+\frac{bc}{\max(c,b+d)}+\frac{ad}{\max(a+c,d)}.
$$

All denominators are positive. Interchanging the axes and relabeling $A,B$ exchanges $(a,b,c,d)$ with $(b,a,d,c)$, so we may assume

$$
w=a+c\ge s=b+d>0.
$$

This is a coordinate interchange, not an arbitrary rotation. For $0\le u\le s$ define

$$
f(u)=\min(a,u)+\frac{cu}{\max(c,s)}+\frac{a(s-u)}{w}.
$$

Since $d\le s\le w$, we have $T(M)=f(b)$ and $S(M)=w+s$. The function is affine on each side of its only possible breakpoint $u=a$. An affine function on a closed interval is a convex combination of its endpoint values, so it suffices to check $u=0$, $u=s$, and $u=a$ when $a\le s$. If a piece has zero length, its single endpoint is already included.

At $u=0$,

$$
f(0)=\frac{as}{w}\le s,\qquad 3f(0)\le3s\le2(w+s).
$$

At $u=s$,

$$
f(s)=\min(a,s)+\min(c,s)\le w,\qquad f(s)\le2s.
$$

Therefore $3f(s)=2f(s)+f(s)\le2w+2s$.

At the breakpoint $u=a$, we have $a\le s$ and $a+c=w\ge s$. Keeping $a,b,c,d$ as the original vertex-coordinate parameters, substitute $u=a$ directly. We must prove

$$
\Phi=2(a+c+s)-3\left(a+\frac{ac}{\max(c,s)}+\frac{a(s-a)}{a+c}\right)\ge0.
$$

If $c\ge s$, direct simplification gives

$$
\Phi=2(c-s)+(s-a)\left(4-\frac{3a}{a+c}\right)\ge0,
$$

because $s-a\ge0$ and $0<a/(a+c)\le1$.

If $c\le s$, both $a+c$ and $s$ are positive. Clearing these denominators gives the exact polynomial certificate

$$
(a+c)s\Phi
=a(s-c)(2a+c-s)+(a+2c+2s)c(s-a).
$$

Every factor on the right is nonnegative: $a>0$, $c\ge0$, $s-c\ge0$, $s-a\ge0$, and $2a+c-s\ge a>0$ because $a+c\ge s$. Thus $\Phi\ge0$. Both cases include equality at the breakpoint of the maximum.

This proves $3T(M)\le2S(M)$. The argument of Section 3 proves the desired inequality for every strictly interior point, and Section 1 covers the boundary. [Taxicab/Algebra.lean](Taxicab/Algebra.lean) verifies the piecewise affine reduction, denominator positivity, and polynomial identities using kernel-checked arithmetic proofs.

## 5. Sharpness for strictly interior points

Take

$$
A=(-1,0),\quad B=(1,0),\quad C=(0,1),\quad P=(0,\varepsilon),\qquad 0<\varepsilon<1.
$$

The noncollinearity determinant is $2$. The barycentric weights are $(1-\varepsilon)/2,(1-\varepsilon)/2,\varepsilon$, all positive and summing to one. The denominators for $BC,CA,AB$ are respectively $1,1,2$.

The vertex distances are $1+\varepsilon,1+\varepsilon,1-\varepsilon$, and the side-line distances are $1-\varepsilon,1-\varepsilon,\varepsilon$. Therefore

$$
S(P)=3+\varepsilon,\qquad T(P)=2-\varepsilon.
$$

For any real $k>3/2$, choose

$$
\varepsilon=\frac{2k-3}{2(k+1)}.
$$

The numerator and denominator are positive, and $2k-3<2(k+1)$, so $0<\varepsilon<1$. Exactly,

$$
k(2-\varepsilon)-(3+\varepsilon)
=2k-3-(k+1)\varepsilon=\frac{2k-3}{2}>0.
$$

Thus $S(P)<kT(P)$. Every larger coefficient fails on a nondegenerate triangle with a strictly interior point. The separate file [Taxicab/Sharpness.lean](Taxicab/Sharpness.lean) proves both exact sums and this quantified sharpness statement.

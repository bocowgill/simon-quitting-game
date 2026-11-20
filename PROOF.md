# A periodic equilibrium in Simon’s four-player quitting game

**Theorem.** In Simon’s four-player quitting game there are tables of independent quitting probabilities and payoffs, of period 1,856, which give an exact Nash equilibrium for the expected terminal reward from every live phase. Given any $\varepsilon>0$, one threshold works for all starting phases, players, larger horizons, and unilateral behavioral deviations. The equilibrium calendar itself is independent of $\varepsilon$. [Lean theorem](PeriodicEquilibrium.lean) · [Game and quantifiers](Challenge.lean) · [Simon’s game](https://doi.org/10.1287/moor.1110.0524)

Number the players modulo four. A player who continues when someone quits receives 100 if her opposite quits and zero otherwise. A quitter receives $-1$ if her successor quits, 1 if she quits alone, and 99 in the remaining cases. When nobody quits the game continues. A terminal reward is repeated starting on the quitting date. Perpetual continuation pays zero. Before absorption there is exactly one possible public history of each length. Thus a behavioral deviation may choose any sequence of conditional stopping probabilities.

## 1. A finite test

Write $p_i(t)$ for the conditional probability of quitting and $K_i(t)=\prod_{j\ne i}(1-p_j(t))$. Independence gives the quitting value $Q_i(t)=100(1-p_{i+1}(t))-1-98K_i(t)$. If player $i$ continues, the expected payment from immediate absorption is $c_i(t)=100p_{i+2}(t)$.

Let $V_i$ be a periodic solution of $V_i(t)=c_i(t)+K_i(t)V_i(t+1)$. Suppose $Q_i(t)\le V_i(t)$, with equality when $p_i(t)>0$, and each player's rivals have a positive chance to stop in a full period. Then the probability of surviving $k$ periods under any deviation is at most $D^k$ for some $D<1$ common to all players and starting phases. The recursion identifies $V_i$ with the value of always waiting, so $0\le V_i\le100$. Iterating the one-date inequalities bounds the expected terminal payoff of every deviation by $V_i$ and gives equality under prescribed play. The bounded surviving term vanishes geometrically.

At any finite truncation a deviator’s expected accrued payoff is at most $V_i$, since replacing the continuation value by zero can only lower its expectation. The corresponding honest loss is at most 100 times the survival probability. Averaging over the first $N$ dates and summing the geometric tails bounds both the honest error and the deviation gain by $100L/((1-D)N)$ for $L=1856$. This bound permits deviations chosen separately for each horizon. [Finite-certificate proof](SimonHeadline.lean) · [Payoff bounds](SimonCalendar.lean)

## 2. The calendar and its equations

In the first block the active players are $0,1,2$ for one date, $0,1$ for 450 dates, $0,1,2$ for one date, and $0,1$ for 12 dates. Each new block advances the roles by one modulo four. The four rotations form a period of 1,856 dates.

In a run of $m$ pair dates, let $X$ be the formal next hazard of player 0 and $Y$ the initial hazard of player 1. Put $r=99/98$, $b=1/2$. At index $j$ use

$$
 x_j=\frac{X}{r^{m-j}+98(r^{m-j}-1)X},\qquad
 y_j=\frac{Yb^j}{1-2Y+2Yb^j}.
$$

These give $x_{j+1}=rx_j/(1-x_j)$ and $y_{j+1}=by_j/(1-y_j)$. The quit values of the pair players are $1-2y_j$ and $1+98x_j$. The two recursions make each current quit value equal the payoff from waiting one date and then taking the next quit value. The formulas for the hazard triples at the two junctions impose the same equality on leaving each pair run, including the transition to the rotated block. Six real variables suffice for all played hazards. [Calendar formulas](Expressions.lean) · [Pair and triple transitions](BaseMatching.lean) · [Exact support in the parameter box](ConcreteHazards.lean)

Compose the affine waiting recursions around the four blocks. Their slopes have product strictly below one, so division by one minus this product gives the periodic waiting values. At each triple, the first two equations match the current quit value to waiting for the first following pair date. The third equates the quit value of role 2 with its periodic waiting value. These are the six components of $F$. A given player’s discrepancy $Q_i-V_i$ propagates on each active run by multiplication by $K_i$. Every such run reaches a triple at which that player occupies role 2 and the third equation kills the discrepancy. This proves equality at every active player-date, even for extremely small positive hazards. [Affine recursion](Affine.lean) · [Finite propagation](ActiveRuns.lean) · [Root-to-table theorem](CertifiedTable.lean)

## 3. A common real zero

Use the dyadic center and radius $2^{-37}$ in the six-dimensional sup norm. All computations use closed intervals with integer endpoints scaled by $2^{768}$ and outward rounding. A quotient can contribute to a certified result only when its denominator interval excludes zero. Exact geometric sums for each pair run replace its 450 or 12 affine updates. Their equality with the original transfers is proved for real parameters in the box. [Center and preconditioner](RootConstants.lean) · [Interval operations](IntervalDivision.lean) · [Transfer identity](FastReal.lean)

For every $x,y$ in the box the arithmetic constructs a matrix $J$ with

$$
 F(x)-F(y)=J(x-y).
$$

For example, the output difference of a product is $(a_x-a_y)b_x+a_y(b_x-b_y)$. The output difference of a quotient is $((a_x-a_y)-(a_y/b_y)(b_x-b_y))/b_x$. These formulas propagate exact linear coefficients for a given ordered pair, enclosed by intervals that work over the whole box. They also apply to equal endpoints. [Secant proof](Secant.lean)

With center $z$, radius $r_0$, and the explicit dyadic matrix $C$, the verified integer comparisons give $\|CF(z)\|_\infty\le r_0/2$ and every row sum of absolute values of $I-CJ$ at most $1/2$. Thus $x\mapsto x-CF(x)$ contracts the closed box into itself. For a permitted $J$ at $z,z$, the same norm estimate makes $CJ$ injective. Since the matrices are square, $C$ is invertible. A fixed point therefore gives an exact zero of $F$. The argument supplies one vector satisfying all six equations simultaneously. [Root-existence proof](RootExistence.lean) · [Finite bounds](RootEnvelope.lean) · [Concrete root](SimonRoot.lean)

## 4. The inactive inequalities

A rational table $l_i(t)$ on the base block closes at $l_i(464)=l_{i+1}(0)$. The kernel checks $l_i(t)\le c_i(t)+K_i(t)l_i(t+1)$ throughout the box for all 1,856 base player-date pairs. It also checks $Q_i(t)\le l_i(t)$ for the 926 inactive pairs. To see why this suffices, take the smallest difference $m=V_i(t)-l_i(t)$ over the cyclic table. The waiting equation and the first inequality imply $m\ge K_i(t)m$ at a minimizing pair, including a block boundary. At each date the first two roles have positive hazards, so every player faces $0\le K_i(t)<1$. A negative $m$ is impossible. Thus $Q_i(t)\le V_i(t)$ at every inactive pair in every rotation. [Checked rows](InactiveChecks.lean) · [Minimum argument](InactivePropagation.lean) · [Concrete inequality](ConcreteInactive.lean)

Applying the finite test to this same zero proves the theorem. The frozen Formal Conjectures trajectory model also verifies the interpretation of these probabilities under arbitrary behavioral deviations and the uniform witness over every initial game state. [FC model](SimonPeriodic.lean) · [Unconditional FC theorem](PeriodicEquilibriumFC.lean)

The theorem concerns Simon’s specified payoff table. Uniform equilibrium existence for every finite stochastic game remains open in this project. [Formal Conjectures #7957](https://github.com/google-deepmind/formal-conjectures/issues/7957)

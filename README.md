# Periodic equilibrium in Simon’s four-player quitting game

**Simon's four-player quitting game admits an equilibrium with a calendar of period 1,856.** From every live phase, the calendar is an exact Nash equilibrium for the expected terminal reward. The same calendar is a uniform equilibrium for expected Cesàro payoffs. For every positive tolerance a single horizon threshold covers all larger horizons, all starting phases, all players, and all unilateral behavioral deviations.

The Lean theorem is `SimonHeadline.periodic_equilibrium`. Its proof constructs four successive 464-date blocks by rotating the players' roles. Each block begins with three players mixing on one date, followed by 450 dates when two adjacent players mix. A second three-player date and 12 more pair dates complete the block. A six-variable root and interval inequalities certify the continuation values and the incentive constraints. This theorem resolves the displayed four-player example. The existence question for arbitrary finite stochastic games remains open in this project. [Simon, *A Topological Approach to Quitting Games*](https://doi.org/10.1287/moor.1110.0524) · [Formal Conjectures #7957](https://github.com/google-deepmind/formal-conjectures/issues/7957)

**Public review draft.** Bo Cowgill directed this investigation. OpenAI Codex was used in the Lean formalization. Human review of this draft is pending. [Read the proof](PROOF.md) · [Inspect the independent theorem statement](Challenge.lean) · [Inspect the Lean proof](PeriodicEquilibrium.lean)

## Game and payoff conventions

Number the players modulo four. At a live date each player independently chooses whether to quit. With no quit, everyone earns zero and the game continues. At the first quit, player $i$ who continues earns 100 if player $i+2$ quits and zero otherwise. A quitter earns −1 if player $i+1$ quits, 1 if quitting alone, and 99 otherwise. This vector is paid on the quitting date and every subsequent date. Forever-continuing play gives zero.

At date $t$, the only live public history consists of $t$ joint all-continue moves. Arbitrary behavioral strategies at live histories therefore reduce to arbitrary per-date hazards. A unilateral deviation may choose a new hazard on every date, including hazards zero and one. The opponents keep their independently randomized hazards. An absorbed initial state has the same fixed payoff under every profile and every positive horizon. The frozen Lean trajectory proof explicitly verifies these statements for the public-history model. [Stochastic-game bridge](SimonPeriodic.lean) · [Frozen game definitions](https://github.com/google-deepmind/formal-conjectures/commit/326cddb8eee07ae19c82d4adee81af8288eac55b)

## Finite certificate

For each phase, certify the value of always continuing, the upper bound on quitting there, and indifference wherever the honest quit probability is positive. For each player, require a positive probability that some rival quits over one period. For any deviation the probability of surviving a whole period is then at most a common $D<1$. The continuation values lie in $[0,100]$. Iterating the one-date inequalities gives terminal optimality and a joint bound of $100L/((1-D)N)$ on honest payoff error and on deviation gain for every phase and horizon $N>0$. Here $L$ is the period. [Definitions and estimates](SimonCalendar.lean) · [Finite-table theorem](SimonHeadline.lean)

## Reproduction

The release project pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Run the two exports separately through Comparator on a supported Linux host.

```sh
lake exe cache get
lake build Challenge Solution
lake comparator --config comparator.json
```

The frozen research replay uses Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The unconditional theorem passed that replay. Its transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. The sole deliberate placeholder in `Challenge.lean` states the goal for Comparator. The solution proves it from the finite calendar construction, root certificate, and all incentive inequalities. The optional target `lake build PeriodicEquilibriumFC` proves the same existence result directly for the frozen public-history stochastic-game trajectory model. The companion passed at both toolchain pins. Its four vendored FC source files match the frozen commit byte for byte. One emits four deprecation warnings at the newer pin. [Unconditional theorem](PeriodicEquilibrium.lean) · [Root certificate](SimonRoot.lean) · [Inactive inequalities](ConcreteInactive.lean)

A second replay on the pinned stable Lean 4.35.0 checked the full transitive solution closure and the same three axioms. Lake resolved every local source in a scratch project with compilation disabled. This project uses the [Apache-2.0 licence](LICENSE). The four vendored FC definitions retain their original [Apache-2.0 licence](FormalConjecturesForMathlib/LICENSE). Registration requires a public repository and an immutable commit. [Palomar submission requirements](https://palomar-registry.org/how-to-submit)

## Local comparison of the release

On November 20, 2026, Lean 4.35.0 Comparator accepted the exported Challenge and Solution for `SimonHeadline.periodic_equilibrium`. The comparison used local export mode on macOS. The registry runs its own sandboxed checks after submission. Independent single-worker runs on the same Solution export succeeded with con-ron in verified mode and with Nanoda. Nanoda printed exactly `propext`, `Quot.sound` and `Classical.choice` and reported zero errors.

| Lean 4.35.0 export | SHA-256 |
|---|---|
| Challenge | `16e087701ceb065abdb2cd79fe6d6ddd31e8ed465fdd8c279ab9614361bfe888` |
| Solution | `b2481e9e66ab632408a7299fa28c21dc6cdf95e07479baecda10f926db5a1dc5` |

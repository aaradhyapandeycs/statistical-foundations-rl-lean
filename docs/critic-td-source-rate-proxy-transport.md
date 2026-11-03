# Independent source-only TD source-rate proxy transport audit

Exact target `.local/TDSourceRateProxyTransportDraft.lean`, SHA-256
`9ee4a1fee7c6719ea8ed342d3b59068d7d1578a8a3e5e304c0d57ba2c881a6b4`.
Exact extension dependency SHA
`31a1638b08f08147d8ef094c40487e35fa5fe5b44fb3c9d9c13c401ab63fa14f`.
Independent source review plus a fresh isolated compile and axiom probe. Lean
source unchanged. The compile evidence below is specific to the frozen hashes
and probe source recorded here.

Verdict: the five inspected definitions/equalities preserve their actual proxy,
exact source-eligible event and actual sampling probability without adding a
source premise. No refuting semantic mismatch was found. This file alone does
not prove any high-probability proxy bound or a final TD theorem.

## Exact source quantity and terminal range

Source `eq:TD-variance-proxy` lines 628–636 defines
barW_t=barEta gamma² Σ_(k=floor(t/2)+1)^t eta_k A_(k+1:t)Var_(Pπ)(V_(k−1)).
Production `tdSquareLateWindowRandomProxy` is precisely this finite row action,
with n=k−1, n<t and floor(t/2)≤n. Thus both even and odd t have the correct
strict late window; eta_(n+1), old V_n, gamma² and the unweighted suffix row all
appear exactly once. It does not accidentally use squared propagator rows or
fold an extra gamma eta factor into the tail row.

The event bound is 16*barEta*H², matching source Lemma
`lemma:TD-variance-proxy-bound`, lines 727–735, after H=1/(1−gamma). Statewise
upper bounds represent its infinity norm only when proxy nonnegativity is
separately available under genuine source rate/barEta conditions. This transport
file intentionally proves equality for arbitrary real barEta and arbitrary
rates; it does not claim upper bounds equal a norm in those broader domains.

Eligibility is exactly T/(c2 logT)≤t. `j:Fin T` with t=j.val+1 ranges over all
positive terminals 1,…,T once, not T/2,…,T or only t=T. On the source domain
T≥2,c2>0 its positive threshold excludes t=0, so this parameterization loses no
eligible terminal. General definitions permit other c2,T values through real
log/division totalization, but no source probability theorem is asserted for
those values. The final consumer must prove eligibility of T if it needs that
terminal; this equality theorem does not assume or derive c2logT≥1.

## Through-T preservation audit

For every summand, n∈range t gives n<t≤T. The active source update k=n+1
therefore satisfies 1≤k≤T, so the extension preserves eta_k. Its old iterate
uses rates 1,…,n and the same `tdSamplesExtend M T data`; the extension theorem
proves equality for that same sample array. The suffix row is the actual
chronological propagator from k through t, hence reads only updates k+1,…,t,
all ≤T. The draft rewrites the exact row through the preservation lemma rather
than postulating equivalent matrices. Its row variance distribution Pπ, gamma,
barEta and state summation are untouched. Inactive guarded summands are zero in
both expressions. No after-T rate is used, and no bound on eta0 is introduced.

The earlier finite-extension review identified unguarded weighted rows k>t as
not necessarily preserved. This proof never uses those objects: active k≤t,
and the production late-terminal row is the plain suffix row. It therefore
avoids that issue correctly. Explicit transport of stochastic increment histories
or conditional-variance sigma algebras is not needed to prove this particular
random-proxy equality; it is an equality of finite measurable functions after
actual conditional moments have already been represented by policy-row variance.
Any other downstream claim about histories still requires its own bridge.

## Event and sampling-law semantics

The event is a subset of exactly `TDSamples State T`, quantifying every state
and every positive terminal, with eligibility retained inside its implication.
Pointwise proxy equality for each t≤T gives equality of whole event sets in both
directions. The final theorem then rewrites the event argument of the *same*
`tdSamplingLaw M π T`. This actual law is the production finite state/time
product law on T+1 row draws, including the unused time-zero coordinate, and is
independent of eta and barEta. There is no pushforward to a different sample
space, no replacement of data and no independence assumption smuggled into this
transport. All used indices 1,…,T remain within the observed finite array.

No [0,1] schedule premise, norm cap, high-probability event premise, conditional
centering claim or source conclusion is added. Equality is valid for any rates,
V0 and data. Hence a separately proved event bound under the zero-tail schedule
can be transported without loss of delta and without a second union bound.
It must still be proved for the exact eligible event and chosen source barEta;
this file provides no event-bound evidence by itself.

## Independent isolated compilation and axiom probe

The exact target above and its finite schedule-extension dependency were
compiled bottom-up in `/tmp/td-source-rate-proxy-transport-20261103` with the
repository-pinned Lean `v4.27.0-rc1`. The dependency
`.local/TDSourceRateFiniteExtensionDraft.lean` remained at SHA-256
`31a1638b08f08147d8ef094c40487e35fa5fe5b44fb3c9d9c13c401ab63fa14f`.
The production dependency
`Formalization.ModelFree.TDSharpEnergyProxy` was resolved from the existing
project build at the inspected source SHA-256
`2b8de611c0a53f9c66be46383466795ff00613deb1bb5bd3876bdb685b09e03e`; its
dependency artifacts were not changed. Both staged modules compiled with exit
code 0 and no source repairs.

Probe source `.local/TDSourceRateProxyTransportAxiomProbe.lean`, SHA-256
`4c97edc3a86b00121ac343b3757e34ce571065919331c9b62b00039a24051be4`, imports
the exact transport module and probes both definitions and all three
theorems. Each reports only the standard Lean axioms `[propext,
Classical.choice, Quot.sound]`:

* `tdSourceEligibleTerminal`
* `tdSourceEligibleProxyEvent`
* `tdSquareLateWindowRandomProxy_eq_sourceRateExtend`
* `tdSourceEligibleProxyEvent_eq_sourceRateExtend`
* `tdSourceEligibleProxyEvent_probability_eq_sourceRateExtend`

This is focused compile/axiom evidence. It does not establish any downstream
high-probability event bound or full project integration.

## Production integration

The production transport module and actual facade passed the 304-module
project check in `verification/20261103T124026811154Z/`; its transitive audit
checked 3,899 project declarations using only the standard three Lean axioms.
This transports an event and its probability unchanged; it does not establish
a high-probability bound for that event.

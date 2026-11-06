# Scope of the MT applicability gate

This is a post-experiment summary. The exact
[pre-registration review draft](https://github.com/gajaka/mt-chain-linear/blob/f9db8d3ec831f2b4d50c62016119aa84508479c1/experiments/crew-mt-applicability/provenance/PROTOCOL-review-draft.md)
is preserved at its recorded revision; the present wording is not that draft.
Historical hashes in the search and review receipts identify the original text.

The proposed first step was a bounded source inspection of native stochastic
retry in Kiro Crew, revision `909e0fc1938261df9c45fd74e86404abf22b5902`.
The question was whether its production lifecycle supplied the state,
product law, failed-event selector and local coordinate replacement required
by an existing MT theorem.

Random timing, a deterministic lease timeout and an externally requested
restart were distinguished from MT resampling. A possible source match
required an explicit map to the theorem's premises before any implementation
or comparative claim. The source gate had a 30-minute ceiling, and an
unresolved map required stopping.

The registered criteria and completed findings are summarized in
[PROTOCOL.md](../PROTOCOL.md) and [REPORT.md](../REPORT.md). The gate ended as
`STOP_UNKNOWN` after 629.682370 seconds: genuine stochastic retry was found,
but the full MT correspondence was not established. No later experimental
stage was run. This is a scoped negative finding about the attempted
instantiation, not an impossibility theorem.

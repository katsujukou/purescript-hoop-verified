(**
 * The interface of the test module: deliberately empty.
 *
 * `Hoop.Runtime.Test` is a leaf -- a dozen `assert_norm`s and the fixtures they
 * run on, each discharged where it stands. The file exists only so that the
 * module may declare `friend Hoop.Runtime.Handlers`, which F* allows only in a
 * module that has an interface: with the handler table abstract,
 * `lookup_clause` has no definition the normaliser can see, and an
 * `assert_norm` running the machine over a literal table gets stuck at the
 * first `perform`.
 *
 * Note what friendship does *not* buy. The tests observe the reference
 * realisation, so what they check is the behaviour of the machine over *that*
 * table; a different realisation is covered by the proofs in
 * `Hoop.Runtime.Metatheory`, which never look inside, and would have to be
 * re-tested on its own terms.
 *)
module Hoop.Runtime.Test

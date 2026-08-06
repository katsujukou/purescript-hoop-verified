(**
 * The interface of the monad-law module: deliberately empty.
 *
 * `Hoop.Runtime.Laws` is a leaf -- its results are consumed by no other module,
 * the reader being the audience rather than the typechecker. The file exists
 * only so that the module may declare `friend Hoop.Runtime.Handlers`, which F*
 * allows only in a module that has an interface: the refutation of algebraicity
 * runs two concrete programs by `assert_norm`, and the normaliser cannot get
 * past a `perform` while the handler table is abstract.
 *
 * The friendship is confined to that counterexample. Every law above it
 * quantifies over an arbitrary handler table and never looks at one.
 *)
module Hoop.Runtime.Laws

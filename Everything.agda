import Categories.2-Category
import Categories.2-Functor
import Categories.Adjoint
import Categories.Adjoint.AFT
import Categories.Adjoint.AFT.SolutionSet
import Categories.Adjoint.Alternatives
import Categories.Adjoint.Compose
import Categories.Adjoint.Construction.EilenbergMoore
import Categories.Adjoint.Construction.Kleisli
import Categories.Adjoint.Equivalence
import Categories.Adjoint.Equivalence.Properties
import Categories.Adjoint.Equivalents
import Categories.Adjoint.Instance.0-Truncation
import Categories.Adjoint.Instance.01-Truncation
import Categories.Adjoint.Instance.Core
import Categories.Adjoint.Instance.PathsOf
import Categories.Adjoint.Instance.PosetCore
import Categories.Adjoint.Instance.StrictCore
import Categories.Adjoint.Instance.StrictDiscrete
import Categories.Adjoint.Mate
import Categories.Adjoint.Monadic
import Categories.Adjoint.Monadic.Crude
import Categories.Adjoint.Monadic.Properties
import Categories.Adjoint.Properties
import Categories.Adjoint.RAPL
import Categories.Adjoint.Relative
import Categories.Adjoint.TwoSided
import Categories.Adjoint.TwoSided.Compose
import Categories.Bicategory
import Categories.Bicategory.Bigroupoid
import Categories.Bicategory.Construction.1-Category
import Categories.Bicategory.Construction.Spans
import Categories.Bicategory.Construction.Spans.Properties
import Categories.Bicategory.Extras
import Categories.Bicategory.Instance.Cats
import Categories.Bicategory.Instance.EnrichedCats
import Categories.Bicategory.Monad
import Categories.Bicategory.Monad.Properties
import Categories.Bicategory.Opposite
import Categories.Category
import Categories.Category.BicartesianClosed
import Categories.Category.BinaryProducts
import Categories.Category.CMonoidEnriched
import Categories.Category.Cartesian
import Categories.Category.Cartesian.Bundle
import Categories.Category.Cartesian.Monoidal
import Categories.Category.Cartesian.Properties
import Categories.Category.Cartesian.SymmetricMonoidal
import Categories.Category.CartesianClosed
import Categories.Category.CartesianClosed.Canonical
import Categories.Category.CartesianClosed.Locally
import Categories.Category.CartesianClosed.Locally.Properties
import Categories.Category.CartesianClosed.Properties
import Categories.Category.Closed
import Categories.Category.Cocartesian
import Categories.Category.Cocartesian.Bundle
import Categories.Category.Cocomplete
import Categories.Category.Cocomplete.Finitely
import Categories.Category.Cocomplete.Finitely.Properties
import Categories.Category.Cocomplete.Properties
import Categories.Category.Complete
import Categories.Category.Complete.Finitely
import Categories.Category.Complete.Finitely.Properties
import Categories.Category.Complete.Properties
import Categories.Category.Complete.Properties.Construction
import Categories.Category.Complete.Properties.SolutionSet
import Categories.Category.Concrete
import Categories.Category.Concrete.Properties
import Categories.Category.Construction.0-Groupoid
import Categories.Category.Construction.Adjoints
import Categories.Category.Construction.Arrow
import Categories.Category.Construction.Cocones
import Categories.Category.Construction.Comma
import Categories.Category.Construction.Cones
import Categories.Category.Construction.Coproduct
import Categories.Category.Construction.Core
import Categories.Category.Construction.Cowedges
import Categories.Category.Construction.EilenbergMoore
import Categories.Category.Construction.Elements
import Categories.Category.Construction.EnrichedFunctors
import Categories.Category.Construction.F-Algebras
import Categories.Category.Construction.Fin
import Categories.Category.Construction.Functors
import Categories.Category.Construction.Grothendieck
import Categories.Category.Construction.GroupAsCategory
import Categories.Category.Construction.KanComplex
import Categories.Category.Construction.KaroubiEnvelope
import Categories.Category.Construction.KaroubiEnvelope.Properties
import Categories.Category.Construction.Kleisli
import Categories.Category.Construction.LT-Models
import Categories.Category.Construction.MonoidAsCategory
import Categories.Category.Construction.MonoidalFunctors
import Categories.Category.Construction.Monoids
import Categories.Category.Construction.ObjectRestriction
import Categories.Category.Construction.Path
import Categories.Category.Construction.PathCategory
import Categories.Category.Construction.Presheaves
import Categories.Category.Construction.Properties.Comma
import Categories.Category.Construction.Properties.EilenbergMoore
import Categories.Category.Construction.Properties.Functors
import Categories.Category.Construction.Properties.Kleisli
import Categories.Category.Construction.Properties.Presheaves
import Categories.Category.Construction.Properties.Presheaves.Cartesian
import Categories.Category.Construction.Properties.Presheaves.CartesianClosed
import Categories.Category.Construction.Properties.Presheaves.Complete
import Categories.Category.Construction.Properties.Presheaves.FromCartesianCCC
import Categories.Category.Construction.Pullbacks
import Categories.Category.Construction.SetoidDiscrete
import Categories.Category.Construction.Spans
import Categories.Category.Construction.StrictDiscrete
import Categories.Category.Construction.Thin
import Categories.Category.Construction.TwistedArrow
import Categories.Category.Construction.Wedges
import Categories.Category.Core
import Categories.Category.Dagger
import Categories.Category.Dagger.Construction.Discrete
import Categories.Category.Dagger.Instance.Rels
import Categories.Category.Diagram.Span
import Categories.Category.Discrete
import Categories.Category.Duality
import Categories.Category.Equivalence
import Categories.Category.Equivalence.Preserves
import Categories.Category.Equivalence.Properties
import Categories.Category.Finite
import Categories.Category.Finite.Fin
import Categories.Category.Finite.Fin.Construction.Discrete
import Categories.Category.Finite.Fin.Construction.Poset
import Categories.Category.Finite.Fin.Instance.Parallel
import Categories.Category.Finite.Fin.Instance.Span
import Categories.Category.Finite.Fin.Instance.Triangle
import Categories.Category.Groupoid
import Categories.Category.Groupoid.Properties
import Categories.Category.Helper
import Categories.Category.Indiscrete
import Categories.Category.Instance.Cartesians
import Categories.Category.Instance.Cats
import Categories.Category.Instance.EmptySet
import Categories.Category.Instance.FamilyOfSetoids
import Categories.Category.Instance.FinCatShapes
import Categories.Category.Instance.FinSetoids
import Categories.Category.Instance.Globe
import Categories.Category.Instance.Groupoids
import Categories.Category.Instance.KanComplexes
import Categories.Category.Instance.LawvereTheories
import Categories.Category.Instance.Monoidals
import Categories.Category.Instance.Nat
import Categories.Category.Instance.One
import Categories.Category.Instance.PartialFunctions
import Categories.Category.Instance.PointedSets
import Categories.Category.Instance.Posets
import Categories.Category.Instance.Properties.Cats
import Categories.Category.Instance.Properties.Posets
import Categories.Category.Instance.Properties.Setoids
import Categories.Category.Instance.Properties.Setoids.CCC
import Categories.Category.Instance.Properties.Setoids.Cocomplete
import Categories.Category.Instance.Properties.Setoids.Complete
import Categories.Category.Instance.Properties.Setoids.LCCC
import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
import Categories.Category.Instance.Quivers
import Categories.Category.Instance.Rels
import Categories.Category.Instance.Setoids
import Categories.Category.Instance.Sets
import Categories.Category.Instance.Simplex
import Categories.Category.Instance.SimplicialSet
import Categories.Category.Instance.SimplicialSet.Properties
import Categories.Category.Instance.SingletonSet
import Categories.Category.Instance.Span
import Categories.Category.Instance.StrictCats
import Categories.Category.Instance.StrictGroupoids
import Categories.Category.Instance.Zero
import Categories.Category.Inverse
import Categories.Category.Lift
import Categories.Category.Monoidal
import Categories.Category.Monoidal.Braided
import Categories.Category.Monoidal.Braided.Properties
import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Closed
import Categories.Category.Monoidal.Closed.IsClosed
import Categories.Category.Monoidal.Closed.IsClosed.Diagonal
import Categories.Category.Monoidal.Closed.IsClosed.Dinatural
import Categories.Category.Monoidal.Closed.IsClosed.Identity
import Categories.Category.Monoidal.Closed.IsClosed.L
import Categories.Category.Monoidal.Closed.IsClosed.Pentagon
import Categories.Category.Monoidal.CompactClosed
import Categories.Category.Monoidal.Construction.Minus2
import Categories.Category.Monoidal.Construction.Product
import Categories.Category.Monoidal.Core
import Categories.Category.Monoidal.Instance.Cats
import Categories.Category.Monoidal.Instance.One
import Categories.Category.Monoidal.Instance.Rels
import Categories.Category.Monoidal.Instance.Setoids
import Categories.Category.Monoidal.Instance.Sets
import Categories.Category.Monoidal.Instance.StrictCats
import Categories.Category.Monoidal.Interchange
import Categories.Category.Monoidal.Interchange.Braided
import Categories.Category.Monoidal.Interchange.Symmetric
import Categories.Category.Monoidal.Properties
import Categories.Category.Monoidal.Reasoning
import Categories.Category.Monoidal.Rigid
import Categories.Category.Monoidal.Star-Autonomous
import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Utilities
import Categories.Category.Product
import Categories.Category.Product.Properties
import Categories.Category.Regular
import Categories.Category.Restriction
import Categories.Category.Restriction.Construction.Trivial
import Categories.Category.Restriction.Instance.PartialFunctions
import Categories.Category.Restriction.Properties
import Categories.Category.RigCategory
import Categories.Category.Site
import Categories.Category.Slice
import Categories.Category.Slice.Properties
import Categories.Category.Species
import Categories.Category.Species.Constructions
import Categories.Category.SubCategory
import Categories.Category.Topos
import Categories.Category.Unbundled
import Categories.Category.Unbundled.Properties
import Categories.Category.Unbundled.Utilities
import Categories.CoYoneda
import Categories.Comonad
import Categories.Comonad.Relative
import Categories.Diagram.Cocone
import Categories.Diagram.Cocone.Properties
import Categories.Diagram.Coend
import Categories.Diagram.Coend.Properties
import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties
import Categories.Diagram.Colimit
import Categories.Diagram.Colimit.DualProperties
import Categories.Diagram.Colimit.Lan
import Categories.Diagram.Colimit.Properties
import Categories.Diagram.Cone
import Categories.Diagram.Cone.Properties
import Categories.Diagram.Cowedge
import Categories.Diagram.Cowedge.Properties
import Categories.Diagram.Duality
import Categories.Diagram.End
import Categories.Diagram.End.Properties
import Categories.Diagram.Equalizer
import Categories.Diagram.Equalizer.Indexed
import Categories.Diagram.Equalizer.Limit
import Categories.Diagram.Equalizer.Properties
import Categories.Diagram.Finite
import Categories.Diagram.KernelPair
import Categories.Diagram.Limit
import Categories.Diagram.Limit.Properties
import Categories.Diagram.Limit.Ran
import Categories.Diagram.Pullback
import Categories.Diagram.Pullback.Limit
import Categories.Diagram.Pullback.Properties
import Categories.Diagram.Pushout
import Categories.Diagram.Pushout.Properties
import Categories.Diagram.ReflexivePair
import Categories.Diagram.SubobjectClassifier
import Categories.Diagram.Wedge
import Categories.Diagram.Wedge.Properties
import Categories.Enriched.Category
import Categories.Enriched.Category.Opposite
import Categories.Enriched.Category.Underlying
import Categories.Enriched.Functor
import Categories.Enriched.NaturalTransformation
import Categories.Enriched.NaturalTransformation.NaturalIsomorphism
import Categories.Enriched.Over.One
import Categories.Enriched.Over.Setoids
import Categories.Functor
import Categories.Functor.Algebra
import Categories.Functor.Bifunctor
import Categories.Functor.Bifunctor.Properties
import Categories.Functor.Cartesian
import Categories.Functor.Cartesian.Properties
import Categories.Functor.Coalgebra
import Categories.Functor.Construction.Constant
import Categories.Functor.Construction.Diagonal
import Categories.Functor.Construction.FromDiscrete
import Categories.Functor.Construction.LiftSetoids
import Categories.Functor.Construction.Limit
import Categories.Functor.Construction.ObjectRestriction
import Categories.Functor.Construction.PathsOf
import Categories.Functor.Construction.SubCategory
import Categories.Functor.Construction.SubCategory.Properties
import Categories.Functor.Construction.Zero
import Categories.Functor.Core
import Categories.Functor.Duality
import Categories.Functor.Equivalence
import Categories.Functor.Fibration
import Categories.Functor.Groupoid
import Categories.Functor.Hom
import Categories.Functor.Hom.Properties
import Categories.Functor.Hom.Properties.Contra
import Categories.Functor.Hom.Properties.Covariant
import Categories.Functor.IdentityOnObjects
import Categories.Functor.Instance.0-Truncation
import Categories.Functor.Instance.01-Truncation
import Categories.Functor.Instance.Core
import Categories.Functor.Instance.Discrete
import Categories.Functor.Instance.SetoidDiscrete
import Categories.Functor.Instance.StrictCore
import Categories.Functor.Instance.Twisted
import Categories.Functor.Instance.UnderlyingQuiver
import Categories.Functor.Limits
import Categories.Functor.Monoidal
import Categories.Functor.Monoidal.Braided
import Categories.Functor.Monoidal.Construction.Product
import Categories.Functor.Monoidal.Properties
import Categories.Functor.Monoidal.Symmetric
import Categories.Functor.Monoidal.Tensor
import Categories.Functor.Power
import Categories.Functor.Power.Functorial
import Categories.Functor.Power.NaturalTransformation
import Categories.Functor.Presheaf
import Categories.Functor.Profunctor
import Categories.Functor.Properties
import Categories.Functor.Representable
import Categories.Functor.Restriction
import Categories.Functor.Slice
import Categories.GlobularSet
import Categories.Kan
import Categories.Kan.Duality
import Categories.Minus2-Category
import Categories.Minus2-Category.Construction.Indiscrete
import Categories.Minus2-Category.Instance.One
import Categories.Minus2-Category.Properties
import Categories.Monad
import Categories.Monad.Duality
import Categories.Monad.Idempotent
import Categories.Monad.Relative
import Categories.Monad.Strong
import Categories.Morphism
import Categories.Morphism.Cartesian
import Categories.Morphism.Duality
import Categories.Morphism.HeterogeneousIdentity
import Categories.Morphism.HeterogeneousIdentity.Properties
import Categories.Morphism.Idempotent
import Categories.Morphism.Idempotent.Bundles
import Categories.Morphism.IsoEquiv
import Categories.Morphism.Isomorphism
import Categories.Morphism.Normal
import Categories.Morphism.Notation
import Categories.Morphism.Properties
import Categories.Morphism.Reasoning
import Categories.Morphism.Reasoning.Core
import Categories.Morphism.Reasoning.Iso
import Categories.Morphism.Regular
import Categories.Morphism.Universal
import Categories.Multi.Category.Indexed
import Categories.NaturalTransformation
import Categories.NaturalTransformation.Core
import Categories.NaturalTransformation.Dinatural
import Categories.NaturalTransformation.Equivalence
import Categories.NaturalTransformation.Extranatural
import Categories.NaturalTransformation.Hom
import Categories.NaturalTransformation.Monoidal
import Categories.NaturalTransformation.Monoidal.Braided
import Categories.NaturalTransformation.Monoidal.Symmetric
import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.NaturalTransformation.NaturalIsomorphism.Equivalence
import Categories.NaturalTransformation.NaturalIsomorphism.Functors
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Braided
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric
import Categories.NaturalTransformation.NaturalIsomorphism.Properties
import Categories.NaturalTransformation.Properties
import Categories.Object.Biproduct
import Categories.Object.Cokernel
import Categories.Object.Coproduct
import Categories.Object.Duality
import Categories.Object.Exponential
import Categories.Object.Initial
import Categories.Object.Kernel
import Categories.Object.Kernel.Properties
import Categories.Object.Monoid
import Categories.Object.NaturalNumber
import Categories.Object.NaturalNumber.Properties.F-Algebras
import Categories.Object.Product
import Categories.Object.Product.Construction
import Categories.Object.Product.Core
import Categories.Object.Product.Indexed
import Categories.Object.Product.Indexed.Properties
import Categories.Object.Product.Limit
import Categories.Object.Product.Morphisms
import Categories.Object.Subobject
import Categories.Object.Subobject.Properties
import Categories.Object.Terminal
import Categories.Object.Terminal.Limit
import Categories.Object.Zero
import Categories.Pseudofunctor
import Categories.Pseudofunctor.Composition
import Categories.Pseudofunctor.Hom
import Categories.Pseudofunctor.Identity
import Categories.Pseudofunctor.Instance.EnrichedUnderlying
import Categories.Tactic.Category
import Categories.Theory.Lawvere
import Categories.Theory.Lawvere.Instance.Identity
import Categories.Theory.Lawvere.Instance.Triv
import Categories.Utils.EqReasoning
import Categories.Utils.Product
import Categories.Yoneda
import Categories.Yoneda.Continuous
import Categories.Yoneda.Properties
import Data.Quiver
import Data.Quiver.Morphism
import Data.Quiver.Paths
import Relation.Binary.PropositionalEquality.Subst.Properties

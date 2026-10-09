/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Source
import SICs.MatrixNotation
import SICs.PowerIndex
import SICs.RestrictedProductUnits

-- Field theory: complex automorphisms, abelian extensions, descent, Kummer, and cyclotomic theory
import SICs.FieldTheory.ComplexGalois
import SICs.FieldTheory.ComplexAutomorphisms
import SICs.FieldTheory.Abelian
import SICs.FieldTheory.GaloisDescent
import SICs.FieldTheory.NormalBasis
import SICs.FieldTheory.Kummer.Basic
import SICs.FieldTheory.Kummer.Duality
import SICs.FieldTheory.Kummer.Degree
import SICs.FieldTheory.Cyclotomic

-- Quantum information: phases, Weyl--Heisenberg operators, r-SICs, small dimensions
import SICs.Quantum.RootsOfUnity
import SICs.Quantum.PhaseSpace
import SICs.Quantum.Characters
import SICs.Quantum.WeylHeisenberg
import SICs.Quantum.DisplacementBasis
import SICs.Quantum.Projectors
import SICs.Quantum.RSIC
import SICs.Quantum.Fiducials
import SICs.Quantum.LowDimensions
import SICs.Quantum.IntegerDisplacement
import SICs.Quantum.DisplacementSums
import SICs.Quantum.GaloisAction

-- The modular group SL(2,Z): characteristics, Hirzebruch--Jung words, Dedekind sums, Rademacher
import SICs.SL2Z.Basic
import SICs.Analysis.Irrational
import SICs.SL2Z.FractionalLinear
import SICs.SL2Z.Characteristics
import SICs.SL2Z.Words
import SICs.SL2Z.WordAccumulator
import SICs.SL2Z.WordPeriods
import SICs.SL2Z.HJExpansion
import SICs.SL2Z.HJStabilizer
import SICs.SL2Z.Rademacher
import SICs.SL2Z.DedekindReciprocity
import SICs.SL2Z.RademacherWord
import SICs.SL2Z.ThetaCharacter
import SICs.SL2Z.RademacherConjugation
import SICs.SL2Z.TorsionCharacteristics
import SICs.SL2Z.CharacteristicDuality

-- Real quadratic arithmetic: discriminants, forms, towers, grids, orders, units
import SICs.Quadratic.FundamentalDiscriminants
import SICs.Quadratic.DegreeTwoAlgebras
import SICs.Quadratic.Forms
import SICs.Quadratic.FormActions
import SICs.Quadratic.ReducedForms
import SICs.Quadratic.FormStabilizers
import SICs.Quadratic.FormOrders
import SICs.Quadratic.Discriminants
import SICs.Quadratic.RealFields
import SICs.Quadratic.Towers
import SICs.Quadratic.ElementForms
import SICs.Quadratic.LatticeUnits
import SICs.Quadratic.HJReduction
import SICs.Quadratic.FundamentalUnits
import SICs.Quadratic.TowerValues
import SICs.Quadratic.DimensionGrids
import SICs.Quadratic.RankOne
import SICs.Quadratic.RankOneFields
import SICs.Quadratic.Orders
import SICs.Quadratic.FundamentalForms
import SICs.Quadratic.ConductorOneElements
import SICs.Quadratic.CanonicalRepresentation
import SICs.Quadratic.OrderUnits
import SICs.Quadratic.ConductorOrders
import SICs.Quadratic.CycleUnit
import SICs.Quadratic.UnitCongruences

-- General analysis: identity theorems, contour shifts, parametric integrals, bounds, ultrametrics
import SICs.Analysis.Sectors
import SICs.Analysis.NearOne
import SICs.Analysis.HyperbolicBounds
import SICs.Analysis.CompactConvergence
import SICs.Analysis.ImproperConvergence
import SICs.Analysis.HolomorphicParametricIntegral
import SICs.Analysis.PeriodLattice
import SICs.Analysis.RemovableQuotient
import SICs.Analysis.RealPowerBounds
import SICs.Analysis.IdentityTheorem
import SICs.Analysis.PuncturedNeighborhood
import SICs.Analysis.StripContour
import SICs.Analysis.FourierContourShift
import SICs.Analysis.RectangleResidues
import SICs.Analysis.VerticalContourShift
import SICs.Analysis.HyperbolicIntegrals
import SICs.Analysis.UltrametricInverse
import SICs.Analysis.UltrametricUnitFiltration

-- Class field theory with its cohomological inputs: completions, idèles, reciprocity, existence
import SICs.DedekindDomain.Ideals
import SICs.DedekindDomain.FractionalIdeals
import SICs.ClassField.RayClassGroup.Basic
import SICs.ClassField.RayClassGroup.Quotient
import SICs.ClassField.Ramification.Basic
import SICs.ClassField.Completion.Basic
import SICs.ClassField.Completion.PlacesAbove
import SICs.FieldTheory.BaseChange
import SICs.ClassField.Completion.Norm
import SICs.ClassField.Completion.WeakApproximation
import SICs.ClassField.Completion.FiniteBaseChange
import SICs.ClassField.Completion.InfiniteBaseChange
import SICs.ClassField.Completion.FiniteConjugation
import SICs.ClassField.Frobenius.Basic
import SICs.ClassField.Frobenius.Tower
import SICs.ClassField.Completion.InfiniteConjugation
import SICs.OrbitStabilizer
import SICs.RepresentationTheory.Basic
import SICs.GroupCohomology.TateLowDegree
import SICs.GroupCohomology.TateHexagon
import SICs.GroupCohomology.Herbrand
import SICs.GroupCohomology.Multiplicative
import SICs.GroupCohomology.Hilbert90
import SICs.GroupCohomology.Filtration
import SICs.RepresentationTheory.IsomorphismDescent
import SICs.GroupCohomology.RationalLattices
import SICs.GroupCohomology.RealLattices
import SICs.RepresentationTheory.PermutedFamily
import SICs.FieldTheory.PermutedAlgebraFamily
import SICs.ClassField.Completion.FiniteDecomposition
import SICs.ClassField.Completion.InfiniteDecomposition
import SICs.ClassField.Completion.KummerDecomposition
import SICs.GroupCohomology.Shapiro
import SICs.GroupCohomology.Pi
import SICs.GroupCohomology.Permutation
import SICs.GroupCohomology.PermutationLattice
import SICs.ClassField.Local.UnitGroups
import SICs.ClassField.Local.IntegralQuotients
import SICs.ClassField.Local.PrincipalUnitPowers
import SICs.ClassField.Local.ValuationSequence
import SICs.ClassField.Local.FinitePowerIndex
import SICs.ClassField.Local.UnitCohomology
import SICs.ClassField.Local.Unramified
import SICs.ClassField.Local.NormIndex
import SICs.ClassField.Local.InfinitePowerIndex
import SICs.ClassField.Local.NormTopology
import SICs.ClassField.Ideles.Basic
import SICs.ClassField.Ideles.Topology
import SICs.ClassField.Ideles.IdealMap
import SICs.ClassField.Ideles.Norm
import SICs.ClassField.Ideles.IdealNorm
import SICs.ClassField.Ideles.Inclusion
import SICs.ClassField.Ideles.FiniteFiber
import SICs.ClassField.Ideles.InfiniteFiber
import SICs.ClassField.Ideles.Galois
import SICs.ClassField.Ideles.SIdeles
import SICs.ClassField.Ideles.Invariants
import SICs.ClassField.Ideles.SIdeleCohomology
import SICs.ClassField.Ideles.NormResidues
import SICs.ClassField.Ideles.RayModulus
import SICs.ClassField.Ideles.Approximation
import SICs.ClassField.Ideles.RaySubgroup
import SICs.ClassField.Ideles.NormApproximation
import SICs.ClassField.Ideles.NormTopology
import SICs.ClassField.SUnits.Basic
import SICs.ClassField.Ramification.Kummer
import SICs.ClassField.Ideles.SIdeleClasses
import SICs.ClassField.SUnits.LogLattice
import SICs.ClassField.SUnits.Valuations
import SICs.ClassField.SUnits.Cohomology
import SICs.ClassField.SUnits.Kummer
import SICs.ClassField.Ideles.FirstInequality
import SICs.ClassField.Frobenius.Generation
import SICs.ClassField.Reciprocity.ArtinMap
import SICs.ClassField.Frobenius.Basis
import SICs.ClassField.Splitting.PrimeCount
import SICs.ClassField.Density.EulerProduct
import SICs.ClassField.Density.PrimeSum
import SICs.ClassField.Density.Splitting
import SICs.ClassField.Frobenius.DegreeOne
import SICs.ClassField.SUnits.LocalPowerClasses
import SICs.ClassField.Ideles.PowerSubgroup
import SICs.ClassField.Ideles.LocalGlobalPower
import SICs.ClassField.Ideles.PowerSubgroupIndex
import SICs.ClassField.Ideles.SecondInequality
import SICs.ClassField.Reciprocity.CongruentIdeles
import SICs.ClassField.Ideles.RayClassComparison
import SICs.FieldTheory.NormSigns
import SICs.ClassField.Reciprocity.Cyclotomic
import SICs.IndependentResidues
import SICs.ClassField.Reciprocity.AuxiliaryFields.Construction
import SICs.ClassField.Reciprocity.AuxiliaryFields.Norms
import SICs.ClassField.Reciprocity.Cyclic
import SICs.ClassField.Reciprocity.Abelian
import SICs.ClassField.Reciprocity.GlobalArtinMap
import SICs.ClassField.Reciprocity.Conjugation
import SICs.ClassField.Reciprocity.RealPlace
import SICs.ClassField.Reciprocity.NormGroups
import SICs.ClassField.Existence.Kummer
import SICs.ClassField.Existence.Descent
import SICs.ClassField.Existence
import SICs.ClassField.Splitting.ComplementaryKummer
import SICs.ClassField.Splitting.Kummer
import SICs.ClassField.Splitting.PrimeDegree
import SICs.ClassField.Splitting.UnramifiedPrimes
import SICs.ClassField.RayClassField.Idelic
import SICs.ClassField.RayClassField.Narrow
import SICs.ClassField.RayClassField.SignClasses

-- Special functions: digamma, Mellin, Barnes, double sine, q-products, Faddeev, five-term integrals
import SICs.SpecialFunctions.Digamma.EulerLimit
import SICs.SpecialFunctions.Digamma.Asymptotics
import SICs.SpecialFunctions.Digamma.Series
import SICs.SpecialFunctions.GammaZetaBounds
import SICs.SpecialFunctions.Mellin.Integration
import SICs.SpecialFunctions.Mellin.ContourShift
import SICs.SpecialFunctions.Mellin.Summation
import SICs.SpecialFunctions.Mellin.TrigammaTransform
import SICs.SpecialFunctions.Mellin.TrigammaInversion
import SICs.SpecialFunctions.Mellin.TrigammaRemainder
import SICs.SpecialFunctions.Mellin.DigammaInversion
import SICs.SpecialFunctions.Mellin.DigammaRemainder
import SICs.SpecialFunctions.BarnesDoubleGamma.Coefficients
import SICs.SpecialFunctions.BarnesDoubleGamma.Product
import SICs.SpecialFunctions.BarnesDoubleGamma.Continuity
import SICs.SpecialFunctions.BarnesDoubleGamma.Rows
import SICs.SpecialFunctions.BarnesDoubleGamma.Normalization
import SICs.SpecialFunctions.BarnesDoubleGamma.Difference
import SICs.SpecialFunctions.DoubleSine.RealIntegral
import SICs.SpecialFunctions.DoubleSine.IntegralIdentities
import SICs.SpecialFunctions.DoubleSine.Identities
import SICs.SpecialFunctions.DoubleSine.ComplexIntegral
import SICs.SpecialFunctions.DoubleSine.ShiftIntegral
import SICs.SpecialFunctions.DoubleSine.ComplexShifts
import SICs.SpecialFunctions.DoubleSine.Gamma
import SICs.SpecialFunctions.QPochhammer.Finite
import SICs.SpecialFunctions.QPochhammer.Infinite
import SICs.SpecialFunctions.QPochhammer.Binomial
import SICs.SpecialFunctions.QPochhammer.Bounds
import SICs.SpecialFunctions.QPochhammer.Divisor
import SICs.SpecialFunctions.QPochhammer.ResidueSeries
import SICs.SpecialFunctions.QPochhammer.Theta
import SICs.SpecialFunctions.QPochhammer.Growth
import SICs.SpecialFunctions.QPochhammer.ThetaModular
import SICs.SpecialFunctions.DoubleSine.SigmaSExponent
import SICs.SpecialFunctions.DoubleSine.QProducts
import SICs.SpecialFunctions.DoubleSine.ShintaniProduct
import SICs.SpecialFunctions.DoubleSine.Comparison
import SICs.SpecialFunctions.DoubleSine.IntegralRepresentation
import SICs.SpecialFunctions.HyperbolicGamma.Basic
import SICs.SpecialFunctions.HyperbolicGamma.EqualPeriods
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodComparison
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodComparisonBounds
import SICs.SpecialFunctions.HyperbolicGamma.Comparison
import SICs.SpecialFunctions.HyperbolicGamma.Asymptotics
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodAsymptotics
import SICs.SpecialFunctions.Faddeev.Generator
import SICs.SpecialFunctions.Faddeev.Divisor
import SICs.SpecialFunctions.Faddeev.Asymptotics
import SICs.SpecialFunctions.Faddeev.ComplexPeriodAsymptotics
import SICs.SpecialFunctions.Faddeev.Modular
import SICs.SpecialFunctions.Faddeev.Word
import SICs.SpecialFunctions.Faddeev.WordBoundary
import SICs.SpecialFunctions.Faddeev.WordShift
import SICs.SpecialFunctions.Faddeev.WordReflection
import SICs.SpecialFunctions.Faddeev.WordDivisor
import SICs.SpecialFunctions.Faddeev.WordContinuation
import SICs.SpecialFunctions.Faddeev.WordLatticeValues
import SICs.SpecialFunctions.Faddeev.ModularGrowth
import SICs.SpecialFunctions.Faddeev.FiveTerm.Algebra
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel
import SICs.SpecialFunctions.Faddeev.FiveTerm.ParameterDomain
import SICs.SpecialFunctions.Faddeev.FiveTerm.ClosedForm
import SICs.SpecialFunctions.Faddeev.FiveTerm.Residues
import SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds
import SICs.SpecialFunctions.Faddeev.FiveTerm.ContourGeometry
import SICs.SpecialFunctions.Faddeev.FiveTerm.Integrability
import SICs.SpecialFunctions.Faddeev.FiveTerm.Holomorphy
import SICs.SpecialFunctions.Faddeev.FiveTerm.ContourLimits
import SICs.SpecialFunctions.Faddeev.FiveTerm.Rectangle
import SICs.SpecialFunctions.Faddeev.FiveTerm.CrossedPoles
import SICs.SpecialFunctions.Faddeev.FiveTerm.Integral
import SICs.SpecialFunctions.Faddeev.FiveTerm.Continuation
import SICs.SpecialFunctions.Faddeev.WordAsymptotics
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Kernel
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Bounds
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Boundary
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Improper
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.ClosedForm
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Identity

-- The Shintani--Faddeev cocycle and its real canonical-word value
import SICs.Cocycle.HJCycleData
import SICs.Cocycle.Domains
import SICs.Cocycle.UpperHalfPlane
import SICs.Cocycle.SigmaS.Basic
import SICs.Cocycle.SigmaS.Reduction
import SICs.Cocycle.SigmaS.Faddeev
import SICs.Cocycle.SigmaS.Reflection
import SICs.Cocycle.BoundaryComparison
import SICs.Cocycle.Word.Basic
import SICs.Cocycle.Word.Shifts
import SICs.Cocycle.Word.Reflection
import SICs.Cocycle.Word.UpperHalfPlane
import SICs.Cocycle.Word.Faddeev
import SICs.Cocycle.Modular.Values
import SICs.Cocycle.Modular.Shifts
import SICs.Cocycle.Modular.Reflection
import SICs.Cocycle.FixedPointCharacter
import SICs.Cocycle.HJCycleProduct
import SICs.Cocycle.ModularBoundary
import SICs.Cocycle.Conjugation
import SICs.Cocycle.FixedPointReduction
import SICs.Cocycle.FixedPointCocycle
import SICs.Cocycle.OrbitBoundary
import SICs.Cocycle.FixedPointQuotient
import SICs.Cocycle.ConductorLowering
import SICs.Cocycle.ConductorDistribution
import SICs.Cocycle.ConductorRelation
import SICs.Cocycle.EtaBoundary
import SICs.Cocycle.ConductorZeroClass

-- Finite quantum dilogarithms of a hyperbolic matrix, its five-term relation, and pseudolattices
import SICs.Dilogarithm.MetricGroup
import SICs.Dilogarithm.FiniteQuantum
import SICs.Dilogarithm.Group
import SICs.Dilogarithm.Values
import SICs.Dilogarithm.FaddeevWord
import SICs.Dilogarithm.FiveTerm.Parameters
import SICs.Dilogarithm.FiveTerm.ClassWindow
import SICs.Dilogarithm.FiveTerm.ResidueKernel
import SICs.Dilogarithm.FiveTerm.Telescoping
import SICs.Dilogarithm.FiveTerm.ResidueBounds
import SICs.Dilogarithm.FiveTerm.Shifted
import SICs.Dilogarithm.FiveTerm.Strip
import SICs.Dilogarithm.FiveTerm.CrossedIdentity
import SICs.Dilogarithm.FiveTerm.CrossedStrip
import SICs.Dilogarithm.FiveTerm.Relation
import SICs.Dilogarithm.FiveTerm.Conjugation
import SICs.Dilogarithm.SubgroupPentagon
import SICs.Dilogarithm.Pseudolattice.Basic
import SICs.Dilogarithm.Pseudolattice.Homothety
import SICs.Dilogarithm.Pseudolattice.Group
import SICs.Dilogarithm.Pseudolattice.Powers
import SICs.Dilogarithm.Pseudolattice.Conjugation
import SICs.Dilogarithm.Pseudolattice.Nested
import SICs.Dilogarithm.Pseudolattice.Distribution

-- Valuations, pseudolattice torsion, Frobenius congruences, and reciprocity
import SICs.Valuation.Basic
import SICs.Valuation.RootsOfUnity
import SICs.FieldTheory.PrimeFieldMoments
import SICs.Valuation.GaussianBinomial
import SICs.Valuation.CosetMoments
import SICs.Valuation.Extension
import SICs.Valuation.NumberField
import SICs.FieldTheory.EmbeddedGalois
import SICs.Dilogarithm.Valuation.PrimaryCoordinates
import SICs.Dilogarithm.Valuation.FourierIntegral
import SICs.Dilogarithm.Valuation.CyclicTranslation
import SICs.Dilogarithm.Valuation.Multiplier
import SICs.Analysis.CharacterSums
import SICs.Dilogarithm.Pseudolattice.GroupMaps
import SICs.Dilogarithm.Pseudolattice.FiveTerm
import SICs.Dilogarithm.Pseudolattice.Saturation
import SICs.Dilogarithm.Pseudolattice.Finiteness
import SICs.Dilogarithm.Pseudolattice.Torsion
import SICs.Dilogarithm.Valuation.Distribution
import SICs.Dilogarithm.Valuation.Units
import SICs.Dilogarithm.Pseudolattice.UnitCircle
import SICs.Dilogarithm.Frobenius.SummandProducts
import SICs.Dilogarithm.Frobenius.SplitTranslation
import SICs.Dilogarithm.Frobenius.SplitLines
import SICs.Dilogarithm.Frobenius.CyclicSummand
import SICs.Dilogarithm.Frobenius.LatticeTranslation
import SICs.Dilogarithm.Frobenius.SplitCongruence
import SICs.Dilogarithm.Reciprocity.IdealTranslation
import SICs.Dilogarithm.Reciprocity.SignedGenerator
import SICs.Dilogarithm.Reciprocity.RayField
import SICs.Dilogarithm.Reciprocity.SignClass
import SICs.Dilogarithm.Reciprocity.UnitaryConjugates

-- Admissible pairs, triples, tuples, and their associated stabilizers
import SICs.Admissible.Pairs
import SICs.Admissible.RankOne
import SICs.Admissible.Triples
import SICs.Admissible.PairTriple
import SICs.Admissible.AssociatedStabilizers
import SICs.Admissible.StabilizerExistence
import SICs.Admissible.FormParity
import SICs.Admissible.ShiftArithmetic
import SICs.Admissible.StabilizerDomain

-- Ghost fiducials, twists, the tuple dilogarithm and twisted convolution, general construction
import SICs.Ghost.OverlapData
import SICs.Ghost.TwistedSummands
import SICs.Ghost.Fiducials
import SICs.Ghost.Shifts
import SICs.Ghost.Phase
import SICs.Ghost.CandidateOverlaps
import SICs.Ghost.CandidateOperator
import SICs.Ghost.Origin
import SICs.Ghost.OverlapReciprocity
import SICs.Ghost.RealOverlaps
import SICs.Ghost.TwistFunctions
import SICs.Ghost.CompatibleTwists
import SICs.Ghost.PhaseConvolution
import SICs.Ghost.ShiftConvolution
import SICs.Ghost.PhaseGalois
import SICs.Ghost.Live
import SICs.Ghost.GhostProjector
import SICs.Ghost.Datum
import SICs.Dilogarithm.AdmissibleTuple
import SICs.Dilogarithm.TupleUnitaryConjugates
import SICs.Dilogarithm.TwistedConvolution
import SICs.Ghost.LiveCandidate
import SICs.Construction

-- Direct principal rank-one proof
import SICs.Principal.Quadratic.Forms
import SICs.Principal.Quadratic.Stabilizers
import SICs.Principal.Admissible
import SICs.Principal.Ghost.DoubleSineProduct
import SICs.Principal.Ghost.Overlaps
import SICs.Principal.Ghost.Candidate
import SICs.Principal.Ghost.Origin
import SICs.Principal.Cocycle.CanonicalReduction
import SICs.Principal.Cocycle.SFReduction
import SICs.Principal.Cocycle.PoleAvoidance
import SICs.Principal.Cocycle.Real
import SICs.Principal.Cocycle.WordIdentification
import SICs.Principal.Cocycle.Word
import SICs.Principal.Cocycle.ModularValues
import SICs.Principal.Ghost.PhasedOverlaps
import SICs.Principal.Construction.GhostProjector
import SICs.Principal.Construction.ShiftSymmetry
import SICs.Principal.Construction.TCCFiniteForm
import SICs.Principal.Dilogarithm.Group
import SICs.Principal.Dilogarithm.Values
import SICs.Principal.Dilogarithm.UnitAction
import SICs.Principal.Dilogarithm.Faddeev.Basic
import SICs.Principal.Dilogarithm.Faddeev.Cocycle
import SICs.Principal.Dilogarithm.Faddeev.Reflection
import SICs.Principal.Dilogarithm.Faddeev.Divisor
import SICs.Principal.Dilogarithm.Faddeev.Continuation
import SICs.Principal.Dilogarithm.Faddeev.Boundary
import SICs.Principal.Dilogarithm.Faddeev.Asymptotics
import SICs.Principal.Dilogarithm.Faddeev.ComplexPeriodAsymptotics
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Kernel
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ParameterDomain
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteParameters
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteCharacteristics
import SICs.Principal.Dilogarithm.Faddeev.LatticeValues
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ComplexPhase
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Boundary
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ComplexBounds
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ImproperBoundary
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ClosedForm
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.IntegralIdentity
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueKernel
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Telescoping
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStripBounds
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ShiftedIdentity
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedIdentity
import SICs.Principal.Dilogarithm.ExactSequence
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ClassWindow
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStrip
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedStrip
import SICs.Principal.Dilogarithm.GhostOverlap
import SICs.Principal.Dilogarithm.Pseudolattice
import SICs.Principal.Dilogarithm.FiveTerm
import SICs.Principal.Dilogarithm.Pentagon
import SICs.Principal.Dilogarithm.TorsionConvolution
import SICs.Principal.Dilogarithm.TwistedConvolution
import SICs.Principal.Dilogarithm.UnitaryConjugates
import SICs.Principal.Construction.Live
import SICs.Principal.Construction.Existence
import MainResults

/-!
# Unconditional SIC existence

This is the umbrella module for a formal proof that Weyl--Heisenberg rank-one SICs exist in every
positive dimension and rank-$r$ SICs exist for every admissible pair of [AFK25]. The proof uses
[RW26], [AFK26], and [RW26b] to discharge the twisted-convolution and real-multiplication-values
(Stark) hypotheses of [AFK25, Theorem 1.46].

## The existence proofs

An admissible tuple packages a real quadratic field, a rank--dimension grid, a binary quadratic
form, and its stabilizers. Special values of the Shintani--Faddeev modular cocycle give normalized
ghost overlaps. The finite five-term relation of [RW26, Radchenko, Wheeler (2026), Theorem 2]
along a letter word at its attractive fixed point supplies the shared analytic input. [AFK26]
then proves the explicit shift $\lambda=-d_j$, making one ghost projector for every admissible
pair. The valuation, Frobenius, and Artin-reciprocity chain of
[RW26b, Radchenko, Wheeler (2026b), Proposition 7] puts all nonzero overlaps on the unit circle
under one ambient automorphism. The entrywise image of the ghost projector under that automorphism
is a live rank-$r$ SIC fiducial (`SICs.Ghost.Live`).

The rank-one endpoint has a shorter direct proof. For the principal form
$Q_d=\langle1,1-d,1\rangle$, [RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]
supplies the shift and [RW26b, Radchenko, Wheeler (2026b), Proposition 7] supplies
unitary conjugates at its pseudolattice. The bridge $F(p/d)\,\tilde\nu_d(p)=\zeta_d(p)$ between
the finite quantum dilogarithm and the phased principal overlap, together with the shared
ghost-to-live argument, finishes dimensions $d>3$; explicit fiducials finish dimensions one, two,
and three. This proof reuses the shared dilogarithm, valuation, and reciprocity layers and the
ghost-to-live argument, but it constructs its own ghost fiducial and does not specialize the
general rank-$r$ construction.

Both existence proofs are unconditional. Full classification is outside the present scope.

## Mathematical layers

The imports above expose the project module by module. Each module documents its own argument and
source correspondence; the folders and top-level files group these subjects:

* `SICs.Source`, `SICs.MatrixNotation`, `SICs.PowerIndex`, `SICs.RestrictedProductUnits`,
  `SICs.OrbitStabilizer`, `SICs.IndependentResidues`: the `@[source]` attribute, square-matrix
  notation, and general facts on subgroup indices, units of restricted products, group actions,
  and independent residues used by class field theory.
* `SICs.FieldTheory`: ambient complex Galois automorphisms, Galois extensions of an embedded
  number field, Galois descent, normal bases, Kummer theory, cyclotomic extensions, prime-codegree
  induction and cyclic separation for finite abelian extensions, base-change norms and their
  signs, permuted algebra families, and prime-field moments.
* `SICs.Quantum`: roots of unity, phase-space arithmetic, displacement operators, projectors,
  general `r`-SIC structure, Weyl--Heisenberg fiducials and overlaps, explicit SICs in dimensions
  one, two, and three, and the Galois action on displacements.
* `SICs.SL2Z`: modular transformations and rational characteristics, Hirzebruch--Jung words and
  expansions with their stabilizers, Dedekind sums and their reciprocity, the Rademacher class
  invariant, the eta and theta multipliers, and fixed characteristics with their lattice
  coordinates.
* `SICs.Quadratic`: fundamental discriminants, binary quadratic forms, their reduction and
  stabilizers, real quadratic fields, fundamental units, dimension towers and rank--dimension
  grids, orders of a given conductor, and their units.
* `SICs.DedekindDomain`, `SICs.RepresentationTheory`, `SICs.GroupCohomology`: ideals and
  fractional ideals, representations and permuted families, Tate cohomology in low degrees,
  Herbrand quotients, Hilbert 90, Shapiro's lemma, and permutation lattices, all inputs to class
  field theory.
* `SICs.ClassField`: ray class groups, completions and decomposition groups, local unit groups
  and norm indices, idèles, `S`-units, the first and second inequalities, Frobenius elements,
  densities of primes, Artin reciprocity, the existence theorem, splitting of primes, and ray
  class fields.
* `SICs.Analysis`: sectors and elementary bounds, uniform and improper convergence, holomorphic
  parametric integrals, identity theorems, contour shifts and the residue theorem on rectangles,
  hyperbolic integrals, character sums, irrational linear relations, and ultrametric analysis.
* `SICs.SpecialFunctions`: digamma asymptotics, gamma and zeta bounds, Mellin integration and
  inversion, the Barnes double gamma, the double sine in integral and Shintani product form,
  q-Pochhammer and theta products, Ruijsenaars' hyperbolic gamma function, the Faddeev generator
  with its modular and word products, and the five-term integral identities of [RW26].
* `SICs.Cocycle`: real sigma-S generator formulas, canonical word values, modular cocycle laws,
  Hirzebruch--Jung cycle products, boundary limits, `GL₂(ℤ)`-conjugation, fixed-point cocycle and
  quotient relations, and the conductor relations.
* `SICs.Valuation`: valuations into `ℝ≥0`, roots of unity, Gaussian binomials, coset moments,
  extension along field extensions, and valuations of `ℂ` above the primes of an embedded number
  field.
* `SICs.Dilogarithm`: metric groups and finite quantum dilogarithms; the finite group of a
  hyperbolic matrix at its attractive fixed point and its values as Faddeev word products; the
  finite five-term relation along a letter word; pseudolattice values with the homothety,
  period-power, conjugation, nested, and distribution laws; and the valuations, Frobenius
  congruences, and reciprocity of the values. All of this is shared by the two unconditional
  proofs. The general construction alone uses the subgroup pentagon relation, the level generator
  of an admissible tuple with its unitary conjugates, and the twisted convolution identity at
  the shift `-d_j` of [AFK26].
* `SICs.Admissible` and `SICs.Ghost`: admissible pairs, triples, and tuples, the construction of an
  associated triple for every pair, associated stabilizers, candidate overlaps, shifts, twists,
  ghost projectors, and their conversion into live fiducials.
* `SICs.Construction`: unconditional live rank-`r` existence for every admissible pair.
* `SICs.Principal`: the explicit principal family, with its own forms and stabilizers,
  admissible tuple, double-sine ghost overlaps, cocycle values, finite quantum dilogarithm with
  the principal Faddeev product, five-term relation, exact sequence, pentagon, twisted convolution
  from [RW26, Radchenko, Wheeler (2026), Theorem 7], and unitary conjugates, and the live
  rank-one construction. The general rank-`r` construction is independent of this layer.

## Real values and fidelity

[AFK25] reaches real quadratic arguments by meromorphic continuation of an upper-half-plane
product. The formal construction uses its finite double-sine representation along the canonical
Hirzebruch--Jung word. `SICs.Cocycle.UpperHalfPlane` explains this word product and its relation to
meromorphic continuation. The generator formulas and their shift and reflection laws are in
`SICs.Cocycle.SigmaS`; `SICs.Cocycle.Word` constructs canonical word values, and
`SICs.Cocycle.Modular` packages the resulting modular values and laws. Their equality with the
upper-half-plane boundary limit is proved in
`SICs.Cocycle.ModularBoundary`.

The primary formalization of each in-scope source statement carries `@[source]` with a
human-readable reference giving the source key, printed item, and page and TeX label where available
(`SICs.Source`); derived declarations keep only their prose citation. The word product defines the
real-line values used by the existence proofs, while upper-half-plane products enter through proved
boundary identities. No unproved equality with a divergent point value is assumed.

The two public existence theorems in `MainResults` depend only on the axioms `propext`,
`Classical.choice`, and `Quot.sound`, as `#print axioms` reports.
-/

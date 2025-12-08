# Common.lean - DEPRECATED

**Status**: ARCHIVED  
**Date**: 2025-10-30  
**Session**: 5.3 Phase 2

## Reason for Deprecation

This file was created during Session 11.2 as an attempt to consolidate shared measurement definitions. However, it was never imported into the main build and became redundant after the comprehensive refactoring in Session 5.3.

## Refactoring History

**Session 5.2**: Identified 12 duplicate definitions across Common.lean, MeasurementGeometry.lean, and NonUnitaryEvolution.lean

**Session 5.3 Phase 1**:
- Created Foundation/ConstraintThreshold.lean with base definitions
- Refactored MeasurementGeometry.lean to use ConstraintThreshold

**Session 5.3 Phase 2**:
- Refactored NonUnitaryEvolution.lean to use both ConstraintThreshold and MeasurementGeometry
- All measurement definitions now have single sources:
  - Base definitions (ConstraintViolations, StateSpace) → ConstraintThreshold
  - Measurement structures/axioms → MeasurementGeometry  
  - Unitary evolution → NonUnitaryEvolution

## Common.lean was never used

- Created in Session 11.2 but never imported in LogicRealismTheory.lean
- All definitions were duplicated in MeasurementGeometry and NonUnitaryEvolution
- Refactoring consolidated everything without needing Common.lean

## Current Architecture

**Foundation Layer**:
- `Foundation/ConstraintThreshold.lean` - Base definitions

**Measurement Layer**:
- `Measurement/MeasurementGeometry.lean` - Measurement operators, axioms, collapse
- `Measurement/NonUnitaryEvolution.lean` - Unitary operators, evolution theorems

**Result**: 0 duplicate definitions, clean module boundaries

## File Preserved For

- Historical reference
- Understanding the evolution of measurement module architecture
- Comparison with final consolidated structure

**DO NOT IMPORT THIS FILE** - Use ConstraintThreshold and MeasurementGeometry instead.

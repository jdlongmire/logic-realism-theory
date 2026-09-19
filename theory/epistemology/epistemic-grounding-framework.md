# Epistemic Grounding Framework

Status: PROVISIONAL FORMALIZATION
Work package: WP-LRT-EGF-0001

## 1. Primitive terms

Let:

- A = actuality
- G = epistemically available given
- E = evidence
- P = premise
- H = hypothesis
- I = inferential operation
- C = conclusion
- S = epistemic subject

These are typed roles. A single proposition or informational state may occupy multiple roles in different contexts, but the roles themselves remain distinct.

## 2. Given

Given(G,S) iff G is epistemically available to S.

Being given establishes availability only:

Given(G,S) does not entail True(G).

Given(G,S) does not entail Evidence(G,H,S).

A given may be true, false, misleading, irrelevant, hypothetical, stipulated, or evidentially significant.

## 3. Evidence

Evidence is relational:

Evidence(G,H,S) iff Given(G,S) and BearsOn(G,H).

BearsOn(G,H) means that G constrains, supports, undermines, entails, contradicts, or otherwise affects the epistemic status of H.

Therefore:

Evidence(G,H,S) entails Given(G,S),

while Given(G,S) does not entail Evidence(G,H,S).

Every evidence item is a given in the relevant epistemic context. Not every given is evidence.

## 4. Premise

Premise(P,I) iff P is admitted as an input to I.

Premise(P,I) does not entail Evidence(P,H,S).

A premise may be evidentially grounded, axiomatic, stipulated, hypothetical, assumed for reductio, or false.

Thus P1,...,Pn |- C establishes an inferential relation without by itself establishing the actuality of the premises or conclusion.

## 5. Hypothesis

Hypothesis(H,S) iff S entertains H as a proposition whose truth is under evaluation.

A hypothesis operates within an already determinate epistemic space. Its rejection does not destroy that space.

## 6. Presupposition

Presupposes(X,Y) iff X cannot be determinately instantiated as X unless Y.

If Y is absent, X fails to be well-posed as X. This is constitutive dependence.

A hypothesis can be rejected while retaining the epistemic operation in which it occurs. A constitutive presupposition cannot be removed while retaining that operation as the same determinate operation.

## 7. Inference

An inference maps admitted premises to a conclusion:

I:(P1,...,Pn) -> C.

For deductive inference:

P1,...,Pn |= C.

Validity concerns the relation between premises and conclusion. It does not establish the truth of the premises.

Valid(I) does not entail True(C) unless the relevant premises are themselves warranted.

Therefore: Validity != Warrant.

## 8. Evidential grounding

Let an argument be J = <P1,...,Pn,C>.

For any premise Pi asserted as describing actuality:

Grounded(Pi,S) iff there exists G such that Evidence(G,Pi,S).

An actuality-directed inference is evidentially grounded when its actuality-asserting premises possess the requisite grounding.

Formal consequence alone can establish P |= Q. It does not establish that Q obtains in actuality without appropriate warrant for P.

## 9. Epistemic grounding chain

The typed structure is:

A -alpha-> G -epsilon-> E -pi-> P -I-> C

where:

- alpha = epistemic access
- epsilon = evidential relevance
- pi = admission as premise
- I = inferential operation

Expanded:

Actuality -> Epistemic Availability -> Evidential Relevance -> Inferential Admission -> Conclusion.

The arrows are typed relations. No stage is identified merely with the next.

## 10. Classes of evidence

Evidence is not restricted to empirical evidence.

Candidate classes include:

- E_emp: empirical evidence
- E_log: logical evidence
- E_math: mathematical evidence
- E_exp: experiential or first-person evidence
- E_test: testimonial evidence

Their warrant conditions may differ. Their common property is relational: each evidence item bears epistemically upon some proposition.

## 11. Candidate constitutive conditions of evidence

Let:

Gamma_E = {identity, differentiation, determinacy, information, relation, truth-aptness, inferential constraint}.

For each candidate Y in Gamma_E, apply the deletion test:

If Y is removed, does Evidence(E,H) become non-instantiable as an evidential relation?

If removal merely changes the evidential conclusion, Y is not thereby a constitutive presupposition.

If removal makes Evidence(E,H) itself indeterminate or unintelligible, then Presupposes(Evidence(E,H),Y) is warranted.

## 12. Candidate constitutive conditions of inference

Let:

Gamma_I = {identity, differentiation, determinacy, relation, logical consequence}.

For each Y in Gamma_I:

If Y is removed, does I(P1,...,Pn) become non-instantiable as inference?

This distinguishes conditions necessary for a particular inference to succeed from conditions necessary for inference to exist as a determinate operation.

## 13. Grounding principle

Provisional principle:

An actuality-directed conclusion is epistemically warranted only insofar as its inferential path terminates in appropriately grounded givens.

Formally, Warranted(C,S) requires an appropriate tuple <G,E,P,I> such that:

Given(G,S)
and Evidence(G,P,S)
and Premise(P,I)
and I(P) -> C,

with corresponding grounding requirements for each actuality-asserting premise.

## 14. Research target

The immediate formal task is to determine Gamma_E and Gamma_I by deletion testing and dependency reduction.

No LRT ontology is to be imported into these candidate sets merely because it is already part of LRT. Any bridge from this epistemic framework to LRT ontology must be earned by the independent survival of candidate constitutive conditions.

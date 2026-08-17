* The appendix should come after references.


>  Detailed human–LLM interaction analysis

The categories in the able for this section are not well defined. 


> Coordination-tooling provenance

This probably isn't important for the target audience.


> Lean listing context

This is an example where the paper is reading more like a reminder for an agent rather than text directed at a reader.

> Resource accounting begins after substantial development,

Is that the right grammar? It reads weird.


> The missingness mechanism is structured

Things like this are examples of LLMs and also ill-specified out of context comments. This entire limitations section reads very poorly.


> Non-digitized material, subscriber-only citation databases, and private correspondence remain limitations, and this search should be repeated immediately before submission.

This is an example of an LLM note-to-self that needs to be removed. The text should not be prescribing what we should do, or why there is existential uncertainty. We simply say: to the best of our knowledge: xyz. No need to drag it out so long. There are many similar "but oh I need to be careful how I phrase this" areas where we should be much breifer.



I don't think we give the modeled numbers of USD and CO2e in the abstract. They are too uncertain to be headline measurements. I wonder if we can calculate KWH instead of CO2e as well... sadly CO2e is too political, although I'm still tempted to push boundaries and put it in. But for now let's do KWH if we have the numbers to support the estimation. We should also be extremely clear that these are lower bound measurements and give the rough extrapolated percent of the project they account for in terms of commits and text length, which can be what we use to extrapolate and we should provide our extrapolated guess somewhere. But a reader should never skim a table and be able to mistake those numbers for total numbers, they have to be qualified as lower bounds in the column names and table captions.


* We do not need to qualify that we used glph substitutions in the listing. Also we should not refer to them as a listing, it should just be referred to as code. 


* "Canonical Lean surface" should just be "Lean signature". The caption should note that the context is omitted, not the text body.

We likely do need to explain in the caption what different pieces of it are. E.g. IsExactSpectralDecomposition, IsTrialResidual. The mapping between lean syntax and the math may not be obvious for the readers, so we need to add more explanation there. Some of that might go into the main prose, some into the caption. 


> A lower formal layer also certifies membership in the relevant norm ideal. The source leaves that
condition implicit when it writes a finite unitarily invariant norm; the displayed declaration presents
the published inequality while retaining the stronger certificate internally.

This sentence could be significant shrunk.


> "canonical declaration"

Should not use that term. Lean signature is fine. We have not established anything about it being canonical, or what that means, so avoid that phrasing.


> The symbols ∥·∥op and ∥·∥F in the listing denote the operator and Frobenius norms

If we don't need to qualify that for the math, we don't need to qualify that for the lean.


> What Had to Be Formalized

This is a LLM-y name. I can't think of anything better "Underlying Foundations" doesn't feel right. "Formalizing Gaps in Mathlib", "Formalizing Missing Foundational Theory" maybe. 

And it should start with something stating how there was a considerable gap between the formal statements we needed and what existed. 


> The appendix gives the exact source-result scope,

If the appendix gives something, link to it with a ref. 


> presentation

This word is not banned, but we should reduce its usage. Sentences where it is used might not be needed. Of course it is for presentation, the reader is already reading the paper.


---


> Formalization as Source Audit

This needs a quick introduction stating of how formalization serves as an audit and can expose previously overlooked errors, or something along that line. 


> The Davis–Kahan headline theorem in Lean

Should rename this "Davis–Kahan Sine Theta Theorem in Lean". And then we should also note that every other theorem in the DK has been formalized. That should also be a major contribution. Use our census to make the careful statement: All (number) major mathematical statement with proofs in CITE PAPER have been formalized in full generality (say what that means) in lean. We should make a similar statement for YWS, but I don't think we have 100% of every major mathematical statement with proof in YWS, so weaken the claim as needed. This should probably be collapsed into one major contribution bullet. Then the surfacing or uncovering of defects and errors is another, and then the foundational formalizations is a 3rd, and I'm debating if the resource accounting is worth claiming as a contribution, but we can do it as a 4th item.


> source-faithful

We likely should not be using "development names" like this in the research paper.


> We track mathematical provenance and formalization provenance separately. Literature citations identify the mathematical source of a theorem.

It feels like this doesn't need to be said like this. 

> The latter include documented ancestry in Spectra [13] and route-map or cross-check use of other Lean developments such as Zhang et al. [14]. 

You are writing this from your perspective where you've discovered content in the repo I gave you. But this is our work together. We say what the ancestry was, not that it was documented, we treat written things in this repo as claims we are making in the paper too.

Note that these and prior comments, also give you license to do other revisions around the paper. Based on what we have discussed so far, what else would you recommend cutting, shrinking, rewording, or reorganizing?


* We likely need some "materials and methods" for formalization or
  formalization process, which can likely be discussed in the appendix with the
table of models that we used, and we can just say we used a ChatGPT chat
interface, Claude Code, and Codex, and no other special tooling. The rough
formalization process was giving the LLM a paper, asking it to transcribe it,
having it decompose the problem in to a roadmaps, fill in the proofs, and then
run it through semantic alignment audits via other LLMs and via humans (i.e. we
looked at a theorem and asked ourselves or an LLM if it mapped to the paper in
full generality, and often the answer was no so we had to continue the cycle),
there was also a search for existing theorems and formalizations component.

we can note we also asked the LLMs to build census tooling after the project started to become large.


In the YWS section, I think it would help if we had theorm -> lean, theorem -> lean structure. 

So we could say: The main contribution has two parts, the first is: then do the theorem and then the lean section for it, and then do section 3.2 and give equation 3 there. We likely move the definition of Define, into the top part of section 3 before 3.1, so 3.1 and 3.2 are focused on the theorems and demonstrating the semantic alignment (without actually saying the words semantic alignment).

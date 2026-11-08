# Lecture style rules

These rules collect preferences Jon directly expressed while reviewing these
lectures. They are not a general presentation style guide or a list of new
agent suggestions. Technical implementation belongs in the
[authoring guide](dkvis/learning/README.md) and
[slide implementation notes](briefs/slide-authoring.md).

## Standalone and evergreen

> “The lectures should stand alone.”
> “I do want to make these videos more ‘evergreen’.”

Write for a viewer who has not participated in the authoring conversation.
A transcript must not answer a prompt or refer to the author's earlier remarks.
For example, replace “your displacement intuition is useful” with a direct
explanation of displacement. This applies to spoken narration as well as
visible slide text.

Give the lecture its own mathematical question and explanation. A connection
to matching or this formalization is fine as an application, but do not rely on
an unexplained reference to “the proof” or “the paper” to supply the motivation.

> “Provenance and historical details of the project ... does not belong there.”

Keep project bookkeeping, implementation ancestry, and repository ownership out
of spoken mathematical lessons. Record those in provenance files and source
notes. Mathematical history can motivate a construction; project history must
not interrupt the explanation of that construction.

## Standalone transcript-first narration (8 November 2026 update)

The standalone requirement is **literal for every TTS recording**, regardless of its
place in the course. Write each spoken mathematical lecture as though it may
be played alone or out of sequence. Do not say “in the previous lecture,”
“last time,” “we covered this earlier,” “in the next lesson,” or similar
references to another episode. Do not announce a sequel in the conclusion.

Reminders and concise reviews are welcome **when they state the mathematics**.
If a proof uses a standard result, give its applicable statement and assumptions,
then explain how it is used. If an example originated in another lecture,
reintroduce the actual vectors, matrix, parameter values, or operator needed
for the current calculation. The listener should never need a prior recording
just to know what an unnamed object or numerical result refers to.

Keep prompting, authoring instructions, curriculum planning, provenance
bookkeeping, repository details, proof-assistant implementation, extraction
instructions, and remarks about what a source file happens to formalize out of
ordinary spoken mathematics. Preserve true attribution and the theorem's exact
hypotheses: name the mathematician, theorem, source paper, or mathematical
construction **when that information actually explains the result**. Put
Lean names, definitions, source locations, verified declaration excerpts,
current dependency locations, and original DKPS donor provenance in the
separate display-only appendix.

For the transcript-first DKPS fundamentals course, the intended listener knows
basic linear algebra and calculus but has **no assumed prior functional
analysis or spectral theory**. Introduce jargon and symbols when they first
matter in the recording. A more advanced slide series may use a different
audience baseline; do not apply its shorthand to the foundations TTS scripts.

Prefer a clear self-contained mathematical question, followed by the setting,
argument, example where helpful, and a conclusion about the theorem and its
limits. Within-lecture callbacks are fine. Don't force every section into the
same rhetorical pattern; avoid contrived hooks or recitations of the whole
course plan. Speak equations naturally, keeping exact formulas and Lean
connections outside the spoken region when necessary for TTS clarity.

**Independent-listening edit test:** extract the narration alone, ignoring
metadata and appendices. Can a new listener identify every named object,
assumption, example and conclusion without being told what was said in any
other lecture? Is every sentence about the mathematics rather than the
instructions used to produce the lecture? This editorial test is separate
from proof verification and from listening to synthesized audio.

## Standalone revision checks (8 November 2026)

Before editing a reference to another recording, identify the mathematical
antecedent it carries. Restore the operator, matrix, vectors, theorem premises,
parameter range, or earlier calculation locally **before** removing chronology.
A cross-episode reference can hide missing mathematics; a text-only substitution
is insufficient when the proof depends on that data.

Read the first substantive paragraph and the last substantive paragraph after
editing, not merely the changed sentence. A deleted recap can strand a pronoun
or leave a leading comma; a deleted sequel announcement can leave an empty or
fragmentary conclusion. End on a consequence or limitation established in the
current recording. An invitation to independently reconstruct that proof is
fine; an announcement about another recording is not.

A series-wide phrase scan must distinguish technical uses of words like
"source" (domain of a linear map, a source defect subspace) from repository
or editorial references. Likewise, "next" may describe the next step **within
the present proof**. Inspect the context rather than blindly deleting all
matches.

For recurring numerical models, each lecture should introduce the model
domain, boundary conditions, parameter restrictions, trial space, chosen basis
when relevant, and the particular residual and gap used. Recompute at least
one defining step when reusing a Gram matrix or Ritz residual, rather than
merely asserting a result calculated in another recording.

The narration extractor validates markers and printable input, not prose,
logic, operator domains, theorem correspondence, or voice quality. Keep
editorial-review disposition, mathematical source checks, compilation checks,
and synthesized-audio acceptance separate in the completion record.

## Pedagogical structure audit (8 November 2026)

Review the mathematical teaching sequence, not just editorial trigger words.
For each standalone recording, check that its opening identifies a definite
mathematical question, its assumptions are supplied before they are needed,
and its definitions support the examples and proof that actually follow.
A successful section should explain why the next lemma or construction is
needed, what it gives, and what remains to be established. End with the
precise result and any limitation that the recording has justified.

References to another episode can be disguised as names: “lecture seventy-two,” “our pinching lecture,” “the earlier Sylvester unit,” or “as we
studied.” Detect spelled-out numbers as well as digits, and substitute the
**applicable mathematical statement**, not merely a generic transition.
Read the resulting paragraph to ensure that the prerequisite or example data
has not been lost and that the new opening or conclusion is grammatical.

For perturbation results, keep apart the source and target subspaces,
spectral clusters, residual operator, gap hypothesis, domain conditions,
angle branch, scalar field, and norm class. A statement about squared ambient
displacement does not on its own yield the same statement about unsquared
trace-norm displacement. Numerical examples require the actual parameters
and defining calculation, especially when they are reused elsewhere.

Track structural findings in a per-lecture disposition record. Lexical
heuristics, section counts, and spoken-word estimates are useful *screening*
signals; they are not grades for mathematical pedagogy, and a lack of a
phrase such as “for example” does not prove that the lesson has no example.
Do not rewrite clear mathematics to satisfy a uniform lecture template.
Distinguish transcript extraction, editorial review, theorem-source checks,
Lean compilation, and listening to synthesized audio in the validation record.

The current TTS course phase is *lecture structure and narration audit*.
Visualizations, slide decks, and a companion presentation are future work.
The present recordings should remain mathematically understandable without
those aids; do not add slide cues or visual dependencies prematurely.

## Human-lecture voice: remove drafting and validation artifacts (8 November 2026)

Judge the **spoken region only** as a finished mathematical lecture. A listener
should hear a mathematician developing an argument, not an assistant reporting
what its author, code repository, or proof assistant did. Keep edit history,
compilation status, theorem-file provenance, machine-checking details, source
wrappers, and validation disclaimers in the companion appendix or review report.
Do not announce those facts in the narration to establish credibility.

Use direct mathematical claims when their hypotheses are satisfied. Avoid
ritual qualifiers such as "we are not claiming," "it would be wrong to claim,"
"this is not just an example," "we have not yet validated," "the source
formalizes," or "the proof is not mere paperwork." Replace each with the
specific fact: a conclusion under its assumptions, the reason a tempting
inference fails, or the exact counterexample. Avoid repetitive contrasts of
the form "not X, but Y" when Y can be stated on its own. Treat phrases such as
"what matters," "the lesson is," "quietly," "silently," "the payoff," and
"the machinery" as editing prompts, **not** forbidden vocabulary; retain one
only when it genuinely helps the explanation.

**Mathematical qualifications stay.** Say what was proved, what remains open,
and why the hypotheses matter. Distinguish a theorem from an unsupported
extension; distinguish an explicit counterexample from a merely failed proof;
retain finite/infinite-dimensional, real/complex, domain, norm-ideal, and
spectral-gap constraints. Do not remove these distinctions merely because the
original phrasing sounds defensive. Prefer, for example, "A pairwise spectral
gap yields the constant-one Hilbert–Schmidt estimate but not the corresponding
operator-norm estimate" over "We cannot claim the stronger bound."

An ordinary human instructor can say "we will prove" or ask the listener to
try a calculation. But dozens of episodes opening "Today we will..." and
closing with prescribed "lessons" sound templated. Vary the rhythm by stating
the problem, the relevant construction, or a precise result directly. A course
introduction and a proof practicum may discuss course goals and exercises;
an ordinary lecture should stay focused on its own subject. Rewrite former
"yesterday" and "later we will" transitions as local mathematical context.

After an edit, read the **whole paragraph** and its neighbors. Check that
removing a disclaimer has not made a stronger theorem appear, stranded a
pronoun, or created an abrupt definition. Treat audit phrase matches as review
candidates, not automated proof that a sentence is defective.

## Mathematical speech and audit feedback (8 November 2026)

Prefer spoken formulas with explicit grouping. Say “twice the sine of half
theta” rather than “two sine theta over two” when the latter could mean a
different expression. Introduce specialized symbols before reading them, and
keep LaTeX-like projection tokens out of narration. Source Markdown emphasis
may aid editing, but the TTS extractor removes its asterisk delimiters.

Preserve mathematical distinctions when checking another model's editorial
feedback. In particular, **ell two** (square-summable sequences) and **L two**
(square-integrable functions) denote different spaces even though their
spoken forms can be similar. A difference in vocabulary need not be a
mistake: “X star” and “X adjoint” can both name an adjoint, and conventional
eponyms should not be truncated solely on a speculative pronunciation risk.
Use a listening test for voice-specific pronunciation changes. Record source
suggestions, decisions, and actual repairs in the non-spoken audit ledger.

## Editorial reports and metadata: report facts directly (8 November 2026)

Apply the same human-writing standard to audit reports, completion summaries,
README files, sidecar descriptions, and recommendations. Describe the change,
show the result, and identify specific remaining work. Avoid ritual assertions
about what a review, citation, Lean build, or source locator does *not* prove.

Prefer a compact record such as “150 narration files pass extraction; 49
historical claims await comparison with the cited passages; Lean compilation
was not run.” Each item has a useful operational meaning. Do not append
paragraphs explaining why a bibliographic link cannot certify a theorem, why
an editorial scan is not a proof, or why a step was not performed unless a
specific reader decision depends on that distinction.

Report statuses in the audit ledger and validation table. The prose should
explain substantive findings, corrections, and priorities, without rehearsing
obvious epistemic limitations. When uncertainty affects a mathematical or
historical claim, name the exact disputed proposition and the evidence needed.
Never substitute confident language for accurate scope. Keep real limitations
where they prevent a misleading concrete conclusion.

**Final editorial check:** delete each sentence whose only contribution is
“this does not establish X” or “we are not claiming Y,” then see whether any
specific information was lost. If the information matters, replace the sentence
with the actual check performed, missing source passage, or affected theorem.

## Audience and scope

> “It's the jargon and shorthand for concepts viewers are not familiar with.”
> “It's not lack of examples that makes following this hard.”

Make the explanation accessible to the stated audience. Explain unfamiliar
concepts and shorthand instead of trying to solve every clarity problem by
adding examples. A learner's walkthrough and a compact specialist presentation
serve different purposes. The requested specialist proof presentation should
not reteach background its audience already knows.

## Introductions, motivation, and summaries

> “Start with the high level true statements we are going to learn.”
> “A few crash course slides ... give them the entire picture, and then the rest ... are details.”

After the title, give a compact overview of the true conclusions the learner
will be able to explain. State their setting and limits in accessible terms;
do not introduce a page of unexplained notation. Use a few connected overview
slides when the topic needs them, then use those conclusions as the roadmap
for the detailed explanation. Revisit the same claims at the end so the viewer
can see what has been justified.

> “Each slide needs some motivation.”
> “Good intros / motivations / a small bit of historical context / summaries.”

Start with the concept and why it matters. Include a small amount of historical
context and end with a summary of what the viewer learned. As the argument
progresses, keep its bigger picture and the current step in view. Explain why a
new construction is being introduced and connect it to information already seen.

> “It starts the discussion with a command to the listener. This is not desirable.”
> “It would be better to start these sort of sections off with a question.”
> “We work to ‘discover’ what we must do in order to answer the question.”

Introduce an explanatory section through its purpose, rather than an
instruction such as “Keep the same trial plane.” A motivating question can
establish what we are trying to find out before presenting a procedure. Develop the construction through
reasoned exploration: what if we try this, what information would it give us,
and does that help answer our question? Explain why each move is useful and
what its answer leaves unresolved. Keep these local questions grounded in the
lecture's larger goal. A question-shaped heading followed immediately by an
unmotivated recipe does not supply this discovery thread.

> “It feels like everything starts with a question now.”
> “Statements of fact can also be pedagogical.”

Use questions at real points of investigation, not as a required opening for
every slide or paragraph. State established facts directly and let conclusions
carry the explanation forward. Mix questions, observations and deductions so
the lecture retains motivation without sounding like a sequence of quizzes.

> “It turns out that <true statement>, let's think about why.”

When a question opens a long derivation, state the result we are working toward
before unpacking it. Let the viewer know both what is true and why its
explanation matters. Do not withhold the destination merely to create suspense.

## Continuity between slides

> “The transition between slides is not very good.”
> “The important information is very abrupt, and we are failing to establish a coherent thread that ties the entire lecture together.”

Write the lecture as a connected explanation. Carry the current question and
what has already been established into the next slide, so the learner has a
reason to follow the next construction. Give important information a lead-in,
then explain its consequence before moving on. The spoken narration must carry
this thread; a motivation subtitle alone does not establish it. Introduce key
formulas as the explanation reaches them, rather than displaying a complete
derivation immediately. Use the same objects and visual relationships to
connect successive steps, without filling the narration with generic transition
phrases.

## Notation, reasoning, and key ideas

> “Grant might also explain notation too. Like I have no idea what fancy L is.”
> “If there are any key ideas, it's likely a good idea to highlight them.”

Explain notation when introducing it. Do not assume a symbol, block matrix,
or named condition is familiar just because it has a short label. Build the
intuition for block structure, not only the algebra that follows from it.

> “It's not enough to just say what it is ... the context ... is primed.”

Introduce the operation or problem in plain language before naming it. For
example, show how small coefficients describe a vector in the original space
before using “lift,” and explain why a small-matrix eigenvalue is being proposed
as a candidate for the original problem before calling it a “Ritz value.” Give
the term a concrete referent and revisit its role when it is used later.
Unpack phrases such as “normal-to-normal action” into which input and output
components are meant. Replace “by symmetry” with the particular symmetry and
the reason it implies the stated relation when that step is not yet familiar.

> “We don't need to explain the difference between transpose and conjugate transpose ... every time.”

Teach the real/complex transpose and adjoint convention in **Before the Series:
Foundations**. Later lectures should state their setting once and use that
convention. Repeat the distinction only when a new argument depends on it.

Spell out why a proof step is available. In the motivating example, requiring
B to commute with P needs an explanation of how such directions are constructed
and why testing them is legitimate. Keep the viewer able to follow and explain
the reasoning, rather than merely recognize the final equation.

Visually highlight key ideas and the general tool being learned.

> “It looks like we applied TTS rules to the slides themselves.”

Keep pronunciation hints confined to synthesis input. Typeset mathematics on
slides normally: for example, use $P=QQ^T$ rather than “P = QQ transpose.”
Spoken renderings of formulas belong in narration, not in displayed equations.

## Visual explanations and consistent colors

> “Tying new information back to information we've already seen.”
> “Judicious and careful animations to really make the points salient.”
> “Connecting these graphs with standardized colors will really help.”

Use animation to make a mathematical relationship or step salient. Connect a
new view to the earlier picture and keep colors consistent across related
graphs, equations, and geometric quantities.

For the matrix-exponential introduction specifically, show scalar and matrix
output graphs, use a small matrix such as a two-by-two example, and highlight
the same changing time t in both views. The velocity interpretation motivates
the topic, but the pure mathematical viewpoint must also be explained.

> “These slides are all lacking in visualization, animation, and color coding.”
> “Voice outputs are better when they are longer.”

Build pictures that explain the mathematical construction, rather than relying
on formulas and text alone. Connect their colors and motion to the narration.
A visual event does not need its own independent vocal generation: preserve
coherent spoken passages when planning synchronized animation.

> “There is no visual cue to tell the student which part of the slide they should be paying attention to wrt to the narration.”

Make the current referent visible through a highlight, pointer, diagram change
or staged calculation that follows the narration. When a passage discusses
several mathematical relationships, supply corresponding visuals rather than
leaving the viewer to infer which part of a static slide is being explained.

## Examples and the general tool

> “Make sure the slide says it's an example and highlight the general tool.”

Label worked examples as examples. Distinguish their particular values from
the reusable statement. When there is room, show the symbolic tool in a box;
otherwise emphasize it with color, boldness, or another clear visual treatment.

## Symbolic facts and Lean companions

> “The symbolic math facts that you learned here and can use in a proof.”
> “Have these correspond to Lean statements.”

Close prerequisite lectures with the reusable symbolic mathematical facts and
then their corresponding Lean statements, especially relevant definitions and
results that landed in Tau Ceti. When showing the Lean, repeat the symbolic
statement beside it so the viewer can connect the two representations.

Use a readable code font, syntax highlighting, and highlights that draw
attention to the relevant part of the Lean statement or proof.

## Numerical considerations are optional

> “Numeric considerations should always be an extra bonus slide.”

When a topic has a non-obvious computational side, add a separate bonus slide
that hints at how the computation is actually done. Keep it distinct from the
core mathematical explanation.

## Study questions

> “Add multiple choice study questions at the end of each video.”

> “The questions at the end of each lecture have been too easy, or contrived.”
> “Maybe we add 2 more so 4 questions for new slides, that check if the listener understands.”

End new lectures with four multiple-choice questions. The first two can check
basic attention and terminology. The additional two should test understanding:
ask the viewer to apply an idea, predict what changes, or distinguish claims in
a new situation. Avoid contrived distractors and questions answerable solely by
recognizing a phrase from the narration.

> “Questions should always be very clear about what object they are referring to.”
> “Let's just have everything take 5 seconds, because we can always pause.”

State the objects, definitions and relevant assumptions needed to answer a
question. Avoid ambiguous labels such as “full residual” without defining the
vector. Distinguish a vector's coordinate entries from its projection onto a
subspace; a zero projection does not mean specific original-coordinate entries
vanish. The question should test the mathematics, not the learner's ability to
guess what the wording means. New and revised study questions use a five-second
thinking pause; viewers can pause playback for longer. Do not lengthen the
pause for a harder question.

## External learning companions

> “Focused external sources like a Wikipedia page, not a sprawling textbook or a dense paper.”
> “Lecture notes from universities or presentations, or YouTube videos on the topic.”

Give each lecture a companion list of external sources that help a learner
understand its material. Link to the particular topic page, lesson, video, or
short set of notes. Explain briefly what each item teaches and where to focus.
Keep this learning list distinct from the research bibliography.

## Title slides, attribution, and history

> “Don't need to read out the entire thing, just say the main concept.”
> “The title slides should have a :robot: emoji on them.”

Give each lecture a title slide. Its narration should name the main concept
briefly and move into the lecture. Show a robot marker and the recorded model
name to disclose LLM generation. Track slide and transcript model provenance.

Git is sufficient for historical tracking. The library does not need to present
all historical versions of the slides or lectures.

## Historical portraits and supporting images

> “Always use images with attribution in slides.”
> “Do not check images into the repo. We check the logic to access the images into the repo.”

Use suitable Creative Commons or otherwise openly reusable portraits and
supporting images to put faces to the people. Show attribution in the slides.
Keep downloaded images outside Git, together with the records needed to transfer
them between machines. People-focused history can be split into several lectures.

## Historical citations and learning references (8 November 2026)

Keep spoken text as direct mathematical exposition. A claim about a publication
(its authorship, date, theorem number, stated hypotheses, historical priority,
reported erratum, or open questions) belongs in a **non-spoken citation sidecar**
with an exact spoken-text anchor and a primary-source audit status. Do not
insert bracketed citations, bibliographic notes, links, citation keys, metadata
tags, source-verification progress, or requests for citations in the narration.
A source link and a checked source passage are distinct audit stages.

Ordinary mathematical assertions are supported by their proofs and the Lean
companion; they do not need an external-reference tag merely because a related
book exists. Add optional further-learning resources separately, describing
what they explain and any material differences in assumptions or scope.
Prefer source links already curated in the earlier lectures, verified
institutional material, and original papers. Those references are displayed
by the eventual learning system, never spoken. The TTS extractor operates
exclusively on the original marked spoken region.

For schema, validator, and editing workflow, see
`draft-stages/tts-lectures/metadata/README.md`.

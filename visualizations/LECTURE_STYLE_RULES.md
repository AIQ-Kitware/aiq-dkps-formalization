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

## Audience and scope

> “It's the jargon and shorthand for concepts viewers are not familiar with.”
> “It's not lack of examples that makes following this hard.”

Make the explanation accessible to the stated audience. Explain unfamiliar
concepts and shorthand instead of trying to solve every clarity problem by
adding examples. A learner's walkthrough and a compact specialist presentation
serve different purposes. The requested specialist proof presentation should
not reteach background its audience already knows.

## Introductions, motivation, and summaries

> “Each slide needs some motivation.”
> “Good intros / motivations / a small bit of historical context / summaries.”

Start with the concept and why it matters. Include a small amount of historical
context and end with a summary of what the viewer learned. As the argument
progresses, keep its bigger picture and the current step in view. Explain why a
new construction is being introduced and connect it to information already seen.

> “It starts the discussion with a command to the listener. This is not desirable.”
> “It would be better to start these sort of sections off with a question.”
> “We work to ‘discover’ what we must do in order to answer the question.”

Open an explanatory section with the question it addresses, rather than an
instruction such as “Keep the same trial plane.” Establish what we are trying
to find out before presenting a procedure. Develop the construction through
reasoned exploration: what if we try this, what information would it give us,
and does that help answer our question? Explain why each move is useful and
what its answer leaves unresolved. Keep these local questions grounded in the
lecture's larger goal. A question-shaped heading followed immediately by an
unmotivated recipe does not supply this discovery thread.

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

Spell out why a proof step is available. In the motivating example, requiring
B to commute with P needs an explanation of how such directions are constructed
and why testing them is legitimate. Keep the viewer able to follow and explain
the reasoning, rather than merely recognize the final equation.

Visually highlight key ideas and the general tool being learned.

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

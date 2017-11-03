//
// Created by Martin Blicha on 03.11.17.
//

#ifndef HIFROG_SUMMARIZATION_CONTEXT_FWD_H
#define HIFROG_SUMMARIZATION_CONTEXT_FWD_H

enum class refinement_modet{
    FORCE_INLINING,
    RANDOM_SUBSTITUTION,
    SLICING_RESULT
    // anything else?
};


enum class init_modet {
    ALL_SUBSTITUTING,
    ALL_HAVOCING
    // anything else?
};

class summarization_contextt;

#endif //HIFROG_SUMMARIZATION_CONTEXT_FWD_H

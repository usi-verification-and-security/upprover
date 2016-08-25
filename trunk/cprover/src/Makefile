DIRS = ansi-c big-int cbmc cpp goto-cc goto-instrument goto-programs \
       goto-symex langapi pointer-analysis solvers util linking xmllang \
       assembler analyses java_bytecode aa-path-symex path-symex musketeer \
       json cegis goto-analyzer jsil symex goto-diff

all: cbmc.dir goto-cc.dir goto-instrument.dir symex.dir goto-analyzer.dir goto-diff.dir

###############################################################################

util.dir: big-int.dir

# everything but big-int depends on util
$(patsubst %, %.dir, $(filter-out big-int util, $(DIRS))): util.dir

.PHONY: languages
.PHONY: clean

cpp.dir: ansi-c.dir linking.dir

languages: util.dir langapi.dir \
           cpp.dir ansi-c.dir xmllang.dir assembler.dir java_bytecode.dir \
           jsil.dir

goto-instrument.dir: languages goto-programs.dir pointer-analysis.dir \
                     goto-symex.dir linking.dir analyses.dir solvers.dir \
                     json.dir

musketeer.dir: goto-instrument.dir

cbmc.dir: languages solvers.dir goto-symex.dir analyses.dir \
          pointer-analysis.dir goto-programs.dir linking.dir \
          goto-instrument.dir

goto-analyzer.dir: languages analyses.dir goto-programs.dir linking.dir \
                   json.dir goto-instrument.dir

goto-diff.dir: languages goto-programs.dir pointer-analysis.dir \
               linking.dir analyses.dir solvers.dir json.dir

goto-cc.dir: languages pointer-analysis.dir goto-programs.dir linking.dir

symex.dir: languages goto-programs.dir pointer-analysis.dir \
           goto-symex.dir linking.dir analyses.dir solvers.dir \
           path-symex.dir goto-instrument.dir

# building for a particular directory

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# generate source files

$(patsubst %, %_generated_files, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_generated_files, %, $@) generated_files
	
generated_files: $(patsubst %, %_generated_files, $(DIRS))

# cleaning

clean: $(patsubst %, %_clean, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \

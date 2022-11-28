RM = rm
FUZZY_NAME = tyinf
FUZZY_NAME_BIN = $(FUZZY_NAME)

.PHONY : clean
clean:
	$(RM) -f ./*.o
	$(RM) -f ./*~
	$(RM) -f ./#*#
	$(RM) -f $(FUZZY_NAME).hi
	$(RM) -f $(FUZZY_NAME_BIN)

RM = rm
FUZZY_NAME = tyinf

.PHONY : clean
clean:
	$(RM) -f ./*.o
	$(RM) -f ./*~
	$(RM) -f ./#*#
	$(RM) -f $(FUZZY_NAME).hi

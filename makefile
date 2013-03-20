CC   = g++ --std=c++11
OBJS = main.o
LIBS = -L~/boost/stage/lib/ -lboost_system

pmcppbsci: $(OBJS)
	$(CC) -Wall $(LIBS) $(INCS) -o pmcppbsci $(OBJS) $(LIBS)

%.o: %.cpp
	$(CC) $(INCS) -c -o $@ $<

clean:
	rm -rf *.o *~ pmcppbsci

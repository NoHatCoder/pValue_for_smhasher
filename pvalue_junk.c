#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <stdlib.h>

#include <stdio.h>

double hashPValueOld2(int hashBits,uint64_t hashes,uint64_t collisions,bool countPairs){
	//With countPairs on each pair of colliding hashes is counted, so for instance 4 identical hashes amount to 6 collisions, as they form 6 pairs.
	//With countPairs off each additional hash of a given values only count once, so 4 identical hashes would only count as 3 collisions.
	//A lot of values are stored in logarithmic form, this prevents over- and under-flow.
	if(collisions==0){
		return 1.0;
	}
	double expected;
	double hashesD=(double)hashes;
	double hashesL=log2(hashesD);
	double possibilitiesL=(double)hashBits;
	double invPossibilities=exp2(-possibilitiesL);
	if(countPairs){
		expected=(double)hashes*((double)hashes-1.0)*0.5*invPossibilities;
	}
	else{
		expected=0.0;
		uint64_t a=2;
		double factorialPartL=hashesL;
		do{
			double incidentChanceL=possibilitiesL;
			double missChanceL=(hashesD-(double)a)*log2(M_E)*invPossibilities;
			incidentChanceL-=missChanceL;
			incidentChanceL-=(double)a*possibilitiesL;
			factorialPartL+=log2((double)(hashes-a+1))-log2((double)a);
			incidentChanceL+=factorialPartL;
			double incidentChance=exp2(incidentChanceL)*(double)(a-1);
			expected+=incidentChance;
			if(((hashesD*invPossibilities)<(double)a) && (incidentChance*1000000000000000000.0<=expected)){
				break;
				//Stop when additional iterations don't change the value.
			}
			a++;
		}while(true);
	}
	printf("%0.15f\n",expected);
	double pValue=0.0;
	double factorialPartL=0.0;
	double factorialPartMinorL=0.0;
	uint64_t a;
	for(a=1;a<collisions;a++){
		double addIn=log2((double)a);
		double oldFactorialPartL=factorialPartL;
		factorialPartL+=addIn;
		factorialPartMinorL-=(factorialPartL-oldFactorialPartL)-addIn;
	}
	a=collisions;
	do{
		double poissonL=0.0;
		double addIn=log2((double)a);
		double oldFactorialPartL=factorialPartL;
		factorialPartL+=addIn;
		factorialPartMinorL-=(factorialPartL-oldFactorialPartL)-addIn;
		poissonL-=factorialPartL+factorialPartMinorL;
		poissonL+=log2(expected)*(double)a;
		poissonL-=log2(M_E)*expected;
		double poisson=exp2(poissonL);
		pValue+=poisson;
		if((expected<(double)a) && (poisson*1000000000000000000.0<=pValue)){
			break;
			//Stop when additional iterations don't change the value.
		}
		a++;
	}while(true);
	return pValue;
}

double hashPValueOld(int hashBits,uint64_t hashes,uint64_t collisions,bool countPairs){
	if(collisions==0){
		return 1.0;
	}
	//With countPairs on each pair of colliding hashes is counted, so for instance 4 identical hashes amount to 6 collisions, as they form 6 pairs.
	//With countPairs off each additional hash of a given values only count once, so 4 identical hashes would only count as 3 collisions.
	double expected;
	double hashesD=(double)hashes;
	double possibilities=ldexp(1.0,hashBits);
	double invPossibilities=1.0/possibilities;
	if(countPairs){
		expected=hashesD*(hashesD-1)*0.5*invPossibilities;
	}
	else{
		expected=0.0;
		uint64_t a=2;
		do{
			double incidentChance=possibilities;
			double missChanceExp=(hashesD-(double)a)*invPossibilities;
			double dividesByED;
			missChanceExp=modf(missChanceExp,&dividesByED);
			uint64_t dividesByE=(uint64_t)dividesByED;
			incidentChance/=exp(missChanceExp);
			uint64_t dividesByPos=a;
			uint64_t factorialMul=a;
			//Order multiplications so that the product does not over- or under-flow.
			while((dividesByE|dividesByPos|factorialMul)!=0){
				while(((incidentChance<=1.0) || ((dividesByE|dividesByPos)==0)) && factorialMul!=0){
					incidentChance*=(double)(hashes-factorialMul+1)/(double)(factorialMul);
					factorialMul--;
				}
				while(((incidentChance>=1.0) || (factorialMul==0)) && dividesByE!=0){
					incidentChance*=(1.0/M_E);
					dividesByE--;
				}
				while(((incidentChance>=1.0) || (factorialMul==0)) && dividesByPos!=0){
					incidentChance*=invPossibilities;
					dividesByPos--;
				}
			}
			incidentChance*=(double)(a-1);
			expected+=incidentChance;
			if((hashesD*invPossibilities<(double)a) && (incidentChance*1000000000000000.0<=expected)){
				break;
				//Stop when additional iterations barely change the value.
			}
			a++;
		}while(true);
	}
	printf("%0.15f\n",expected);
	double pValue=0.0;
	uint64_t a=collisions;
	do{
		//Compute the cumulative probability mass function.
		double dividesByED;
		double expFraction=modf(expected,&dividesByED);
		uint64_t dividesByE=(uint64_t)dividesByED;
		double poisson=1.0/exp(expFraction);
		uint64_t factorialDiv=a;
		uint64_t expectedMul=a;
		//Order multiplications so that the product does not over- or under-flow.
		while((dividesByE|factorialDiv|expectedMul)!=0){
			while(((poisson<=1.0) || ((factorialDiv|dividesByE)==0)) && expectedMul!=0){
				poisson*=expected;
				expectedMul--;
			}
			while(((poisson>=1.0) || (expectedMul==0)) && factorialDiv!=0){
				poisson/=(double)factorialDiv;
				factorialDiv--;
			}
			while(((poisson>=1.0) || (expectedMul==0)) && dividesByE!=0){
				poisson*=(1.0/M_E);
				dividesByE--;
			}
		}
		pValue+=poisson;
		if((expected<(double)a) && (poisson*1000000000000000.0<=pValue)){
			break;
			//Stop when additional iterations barely change the value.
		}
		a++;
	}while(true);
	return pValue;
}

void* pValueTable[65536];

double hashPValue(int hashBits,uint64_t hashes,uint64_t collisions,bool countPairs,double* expectedOut){
	if(collisions==0){
		return 1.0;
	}
	//With countPairs on each pair of colliding hashes is counted, so for instance 4 identical hashes amount to 6 collisions, as they form 6 pairs.
	//With countPairs off each additional hash of a given values only count once, so 4 identical hashes would only count as 3 collisions.
	double expected;
	double hashesD=(double)hashes;
	double possibilities=ldexp(1.0,hashBits);
	double invPossibilities=1.0/possibilities;
	if(countPairs){
		expected=hashesD*(hashesD-1)*0.5*invPossibilities;
	}
	else{
		if((hashesD>possibilities) || true){
			expected=hashesD-possibilities+possibilities*pow(sqrt(1.0-invPossibilities)/M_E,hashesD*invPossibilities);
		}
		else{
			expected=0.0;
			uint64_t a=2;
			do{
				double incidentChance=possibilities*pow(sqrt(1.0-invPossibilities)/M_E,(hashesD-(double)a)*invPossibilities);
				uint64_t dividesByPos=a;
				uint64_t factorialMul=a;
				//Order multiplications so that the product does not over- or under-flow.
				while((dividesByPos|factorialMul)!=0){
					while(((incidentChance<=1.0) || (dividesByPos==0)) && factorialMul!=0){
						incidentChance*=(double)(hashes-factorialMul+1)/(double)(factorialMul);
						factorialMul--;
					}
					while(((incidentChance>=1.0) || (factorialMul==0)) && dividesByPos!=0){
						incidentChance*=invPossibilities;
						dividesByPos--;
					}
				}
				incidentChance*=(double)(a-1);
				expected+=incidentChance;
				if(incidentChance*1000000000000000.0<=expected){
					break;
					//Stop when additional iterations barely change the value.
				}
				a++;
			}while(true);
		}
	}
	if(expectedOut!=(double*)0){
		*expectedOut=expected;
	}
	
	if((!countPairs) && (hashBits<=32) && (expected*hashesD<100000000000.0)){
		//Use an exact p-value table in cases where the Poisson distribution may be inaccurate, and the processing power required is not too much.
		void* tableEntry=(void*)0;
		bool pleaseFree=false;
		uint64_t a;
		int64_t b;
		for(a=0;a<65536;a++){
			//Search for a matching entry in the global table
			if(pValueTable[a]==(void*)0){
				break;
			}
			uint64_t* intEntry=(uint64_t*)(pValueTable[a]);
			if((intEntry[0]==hashBits) && (intEntry[1]==hashes)){
				tableEntry=pValueTable[a];
				break;
			}
		}
		if(tableEntry==(void*)0){
			//Create a missing entry
			uint64_t entries=(uint64_t)(expected*3.0);
			if(entries<1000){
				entries=1000;
			}
			double* probabilityTable=calloc(entries,8);
			probabilityTable[0]=1.0;
			int64_t rangeBegin=0;
			int64_t rangeEnd=1;
			for(a=0;a<hashes;a++){
				for(b=rangeEnd;b>rangeBegin;b--){
					probabilityTable[b]=probabilityTable[b]*(1.0-invPossibilities*(double)(a-b))+probabilityTable[b-1]*invPossibilities*(double)(a-b+1);
				}
				probabilityTable[rangeBegin]=probabilityTable[rangeBegin]*(1.0-invPossibilities*(double)(a-rangeBegin));
				if(probabilityTable[rangeBegin]<0.000000000000000001){
					rangeBegin++;
				}
				if((probabilityTable[rangeEnd]>0.000000000000000001) && (rangeEnd<entries-1)){
					rangeEnd++;
				}
			}
			void* storedTable=malloc(8*(rangeEnd-rangeBegin+5));
			uint64_t* storedTableI=(uint64_t*)storedTable;
			double* storedTableD=(double*)storedTable;
			storedTableI[0]=hashBits;
			storedTableI[1]=hashes;
			storedTableI[2]=rangeBegin;
			storedTableI[3]=rangeEnd;
			double pSum=0.0;
			for(b=rangeEnd;b>=rangeBegin;b--){
				pSum+=probabilityTable[b];
				storedTableD[4+b-rangeBegin]=pSum;
			}
			free(probabilityTable);
			tableEntry=storedTable;
			pleaseFree=true;
			for(a=0;a<65536;a++){
				//Search for a matching entry again, another thread may have created it simultaneously. There is a small chance that a race condition will lead to leaking memory.
				if(pValueTable[a]==(void*)0){
					pValueTable[a]=storedTable;
					pleaseFree=false;
					break;
				}
				uint64_t* intEntry=(uint64_t*)(pValueTable[a]);
				if((intEntry[0]==hashBits) && (intEntry[1]==hashes)){
					tableEntry=pValueTable[a];
					free(storedTable);
					pleaseFree=false;
					break;
				}
			}
		}
		uint64_t* tableEntryI=(uint64_t*)tableEntry;
		double* tableEntryD=(double*)tableEntry;
		double pValue;
		if(collisions>tableEntryI[3]){
			pValue=0.0;
		}
		else if(collisions<tableEntryI[2]){
			pValue=1.0;
		}
		else{
			pValue=tableEntryD[4+collisions-tableEntryI[2]];
		}
		if(pleaseFree){
			free(tableEntry);
		}
		return pValue;
	}
	else{
		uint64_t factorialDiv=collisions;
		uint64_t expectedMul=collisions;
		double dividesByED;
		double expFraction=modf(expected,&dividesByED);
		uint64_t dividesByE=(uint64_t)dividesByED;
		double poisson=exp(-expFraction);
		while((dividesByE|factorialDiv|expectedMul)!=0){
			while(((poisson<=1.0) || ((factorialDiv|dividesByE)==0)) && expectedMul!=0){
				poisson*=expected;
				expectedMul--;
			}
			while(((poisson>=1.0) || (expectedMul==0)) && factorialDiv!=0){
				poisson/=(double)factorialDiv;
				factorialDiv--;
			}
			while(((poisson>=1.0) || (expectedMul==0)) && dividesByE!=0){
				poisson*=(1.0/M_E);
				dividesByE--;
			}
		}
		double pValue;
		if((double)collisions>expected){
			pValue=poisson;
			uint64_t a=collisions+1;
			do{
				poisson*=expected/(double)a;
				pValue+=poisson;
				a++;
			}while(!(poisson*1000000000000000.0<=pValue));
		}
		else{
			double invExpected=1.0/expected;
			double invPValue=0.0;
			uint64_t a=collisions;
			while((a>=1) && !(poisson*1000000000000000.0<=pValue)){
				poisson*=(double)a*invExpected;
				invPValue+=poisson;
				a--;
			}
			pValue=1.0-invPValue;
		}
		return pValue;
	}
}

double coinPValue(uint64_t flips,uint64_t heads){
	if(flips<2*heads){
		heads=flips-heads;
	}
	double p=1.0;
	uint64_t divide2=flips;
	uint64_t factorialMul=heads;
	while((factorialMul!=0) || (divide2!=0)){
		if(((p>=1.0) || (factorialMul==0)) && divide2>=50){
			p*=0x1p-50;
			divide2-=50;
		}
		if(((p>=1.0) || (factorialMul==0)) && divide2>=1){
			p*=0.5;
			divide2--;
		}
		if(((p<=1.0) || (divide2==0)) && factorialMul>=1){
			p*=(double)(flips-factorialMul+1)/(double)factorialMul;
			factorialMul--;
		}
	}
	double pValue=p;
	int64_t a;
	for(a=heads;a>0;a--){
		p*=(double)a/(double)(flips-a+1);
		pValue+=p;
		if(p*1000000000000000.0<=pValue){
			break;
		}
	}
	return pValue;
}

#include <windows.h>
#include <bcrypt.h>

void simulate(int hashBits,uint64_t hashes,uint64_t runs){
	uint8_t count[65536];
	uint32_t collisionCountsA[65536];
	uint32_t collisionCountsB[65536];
	double avgCollisionsA=0.0;
	double avgCollisionsB=0.0;
	memset((void*)collisionCountsA,0,65536*4);
	memset((void*)collisionCountsB,0,65536*4);
	uint64_t possibilities=1<<hashBits;
	uint64_t possibilitiesMask=possibilities-1;
	uint64_t a,b;
	uint8_t randomBuffer[65544];
	uint64_t randomBufferNext=65536;
	for(a=0;a<runs;a++){
		uint64_t collisionsA=0;
		uint64_t collisionsB=0;
		memset(count,0,possibilities);
		for(b=0;b<hashes;b++){
			if(randomBufferNext>=65536){
				randomBufferNext=0;
				BCryptGenRandom((void*)0,randomBuffer,65536,2);
			}
			uint64_t value=(*((uint64_t*)(randomBuffer+randomBufferNext)))&possibilitiesMask;
			randomBufferNext+=2;
			collisionsA+=(count[value]!=0);
			collisionsB+=count[value];
			count[value]++;
		}
		if(collisionsA<65536){
			collisionCountsA[collisionsA]++;
		}
		if(collisionsB<65536){
			collisionCountsB[collisionsB]++;
		}
		avgCollisionsA+=(double)collisionsA/(double)runs;
		avgCollisionsB+=(double)collisionsB/(double)runs;
	}
	uint64_t pValue=runs;
	for(a=0;a<65536;a++){
		if(collisionCountsA[a]){
			printf("%llu collisionsA, p-value: %llu\n",a,pValue);
			pValue-=collisionCountsA[a];
		}
	}
	printf("Average: %0.15f\n",avgCollisionsA);
	pValue=runs;
	for(a=0;a<65536;a++){
		if(collisionCountsB[a]){
			printf("%llu collisionsB, p-value: %llu\n",a,pValue);
			pValue-=collisionCountsB[a];
		}
	}
	printf("Average: %0.15f\n",avgCollisionsB);
}

int main(){
	double p;
	double e;
	/*
	p=hashPValue(24,1000000,166,false);
	printf("%0.15f\n",p);
	p=hashPValue(24,1000000,166,true);
	printf("%0.15f\n",p);
	p=hashPValue(24,4000000,166,false);
	printf("%0.15f\n",p);
	p=hashPValue(24,4000000,166,true);
	printf("%0.15f\n",p);
	p=hashPValue(32,1000000,166,false);
	printf("%0.15f\n",p);
	p=hashPValue(32,1000000,166,true);
	printf("%0.15f\n",p);
	p=hashPValue(32,1000000,116,true);
	printf("%0.15f\n",p);
	p=hashPValueOld2(32,1000000,116,true);
	printf("%0.15f\n",p);
	p=hashPValue(32,1000000,117,true);
	printf("%0.15f\n",p);
	p=hashPValueOld2(32,1000000,117,true);
	printf("%0.15f\n",p);
	p=hashPValue(1,100,35*34/2+65*64/2,true);
	printf("%0.15f\n",p);
	p=hashPValue(6,100,120,true);
	printf("%0.15f\n",p);
	p=hashPValue(6,100,77,false);
	printf("%0.15f\n",p);

	p=hashPValue(16,1000,15,false);
	printf("%0.15f\n",p);	
	p=hashPValueOld(16,1000,15,false);
	printf("%0.15f\n",p);	
	p=hashPValueOld2(16,1000,15,false);
	printf("%0.15f\n",p);	
	p=hashPValue(16,1000,15,true);
	printf("%0.15f\n",p);	
	//simulate(16,1000,1000000);
	simulate(8,100,1000000);
	p=hashPValue(8,100,30,true);
	printf("%0.15f\n",p);
	p=hashPValue(8,100,25,false);
	printf("%0.15f\n",p);
	*/
	//simulate(16,20000,1000000);
	p=hashPValue(16,20000,2888,false,&e);
	printf("%0.15f %0.15f\n",p,e);
	p=hashPValue(16,20000,2650,false,&e);
	printf("%0.15f %0.15f\n",p,e);
	p=hashPValue(16,20000,3210,true,&e);
	printf("%0.15f %0.15f\n",p,e);
	
	p=coinPValue(10,7);
	printf("%0.15f\n",p);
	p=coinPValue(10,6);
	printf("%0.15f\n",p);
	p=coinPValue(10,5);
	printf("%0.15f\n",p);
	p=coinPValue(10,4);
	printf("%0.15f\n",p);
	p=coinPValue(10,3);
	printf("%0.15f\n",p);
	p=coinPValue(10,2);
	printf("%0.15f\n",p);
	p=coinPValue(10,1);
	printf("%0.15f\n",p);
	p=coinPValue(10,0);
	printf("%0.15f\n",p);
	p=coinPValue(10001,5000);
	printf("%0.15f\n",p);
}
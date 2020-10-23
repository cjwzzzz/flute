#include <stdio.h>
#include <stdlib.h>
#include "flute.h"
#include "string.h"
//extern int pnum;
void printBranch(Branch branch) {
    printf("(%d, %d), n = %d\n", branch.x, branch.y, branch.n);
}

void printTree(Tree tree) {
    int i;
    printf("Degree: %d\n", tree.deg);
    printf("Length: %d\n", tree.length);
    for ( i = tree.deg; i < 2 * tree.deg - 2; i++) {
        printBranch(tree.branch[i]);
        // if(tree.branch[i].n == 0)
            // break;
    }
}
void func_free(Branch **p){
	free(*p);
	*p=NULL;
	
	}


void generateData(char* file_in,char* filename) { //,char* filename
    FILE *fin;
    FILE *fp;
    int count;
    
    
    int currentline=0;
    int x[5000],y[5000];
    int z[5000];
    int d;
    long int netname;
    int j0=0;
    int i0=0;
    int i,j;
    int xtemp,ytemp;
 
   
    Tree flutetree; 
    struct csoln *p; 
    char line[9999]; 
    readLUT();   
    
#pragma warning(disable : 4996)
    if((fin=fopen(file_in, "r")) == NULL) {
        printf(" Cannot open: %s file", file_in);
        
    }
    
    if((fp=fopen(filename, "w")) == NULL) {
        printf(" Cannot open: %s file", filename);
        
    }
    //ch=fgetc(fin);
    //count=(int) (ch);
    while(!feof(fin)){
	
	
        fgets(line, 1000, fin);
        if(currentline==0){
	    sscanf(line,"%d%*s\n",&count);
            currentline=1111;
            //printf("%d \n", count);
            
	    continue;
        }
        else{

            
	    if(currentline==99990){
	    currentline=0;
	    break;}
	    if( strstr(line,":") ){
	    sscanf(line,"%*s\t:\t%d\t%*d\n",&netname);
	    sscanf(line,"%*s\t:\t%*d\t%d\n",&d);
	    
	    //printf("%d \n", netname);
	    continue;
	    }
	    else{
	    
	    if(d>=2){
            sscanf(line,"%d\t%*d\t%*d\n",&z[j0]);//printf("%d ",z[j0]);
	    j0++;
	    sscanf(line,"%*d\t%d\t%*d\n",&z[j0]);//printf("%d \n",z[j0]);
	    j0++;
	    sscanf(line,"%*d\t%*d\t%d\n",&z[j0]);//printf("%d \n",z[j0]);
	    j0++;
	    if(j0==3*d){


	    	for (i0=0; i0< d; i0++){
			x[i0]=z[3*i0];
			y[i0]=z[3*i0+1];
		
	    	}
	    //fgetc(fin);
	        
            	
           	 for ( i = 0; i < d; i++) {
                	for ( j = i + 1; j < d; j++) {
                    	if (x[i] > x[j] || (x[i] == x[j] && y[i] > y[j])) {
                        	 xtemp = x[i];
                       	  ytemp = y[i];
                       	 x[i] = x[j];
                         y[i] = y[j];
                       	 x[j] = xtemp;
                       	 y[j] = ytemp;
                    	}
                        }
            	 }
            


            flutetree = flute(d, x, y, ACCURACY);
           for ( i = d; i < 2 * d - 2; i++) {
                for ( j = i + 1; j < 2 * d - 2; j++) {
                    if (flutetree.branch[i].x > flutetree.branch[j].x || (flutetree.branch[i].x == flutetree.branch[j].x && flutetree.branch[i].y > flutetree.branch[j].y)) {
                         xtemp = flutetree.branch[i].x;
                         ytemp = flutetree.branch[i].y;
                        flutetree.branch[i].x = flutetree.branch[j].x;
                        flutetree.branch[i].y = flutetree.branch[j].y;
                        flutetree.branch[j].x = xtemp;
                        flutetree.branch[j].y = ytemp;
                    }
                }
            }



        //.......................................................改


    




	    /*printf("%d %d %d ",netname,d*flutetree.length,d);*/
	    fprintf(fp,"%d %d %d ",netname,d*flutetree.length,d);
	    
            
            for( i = 0; i < d; i++) {
                fprintf(fp, "%d %d %d ", z[3*i], z[3*i+1],z[3*i+2]);
            }  //打印输入
     

            fprintf(fp,"fltuelength : %d ", flutetree.length);
	    if(d>2){
            fprintf(fp, "output: ");
            for ( i = d; i < 2 * d - 2; i++) {
            /*int outx = flutetree.branch[i].x;
            int outy = flutetree.branch[i].y;
            int idx = -1;
            int idy = -1;
            for (int j = 0; j < d; j++) {
                if (outx == x[j]) {
                    idx = j;
                    break;
                }
            }
            for (int j = 0; j < d; j++) {
                if (outy == y[j]) {
                    idy = j;
                    break;
                }
            }
            if (idx == -1 || idy == -1) {
                printf("idx or idy not found\n");
            }*/
            fprintf(fp, "%d %d ", flutetree.branch[i].x,flutetree.branch[i].y);

        }
	}
	    



            fprintf(fp, "\n");
            j0=0;
	    //func_free(flutetree.branch);
	    free(flutetree.branch);flutetree.branch=NULL;
	    /*for(i=0;i<pnum;i++)
	    {p--;
	    }
	    pnum=0;free(p);p=NULL;*/
	    //pnum=0;

	    
            /*for(int i = 0; i< d; i++) {
                printf("%d %d ", x[i], y[i]);
            }
	    for (int i = d; i < 2 * d - 2; i++) {
                printf("%d %d ", flutetree.tree.branch[i].x, flutetree.tree.branch[i].y);
            }
	    printf("\n");*/
	    
            
	}
	else continue;
        }else continue;
    	}
	}
	}	
    fclose(fin);
    fclose(fp);
    
}

int main()
{
    // char* dir = "data";
    // mkdir(dir);
    // generateData("data/rsmt_5_train_6.txt", 10000, 2018);
    // generateData("data/rsmt_5_test_6.txt", 10000, 2019);
    // generateData("data/rsmt_4_test_dup5.txt", 10000, 2019);
    generateData("../inputfile/benchmark_cad1_18.txt","../inputfile/flute_100_test.txt");// 

    // int d=0;
    // int x[MAXD], y[MAXD];
    // Tree flutetree;
    // int flutewl;
    //
    // while (!feof(stdin)) {
    //     scanf("%d %d\n", &x[d], &y[d]);
    //     d++;
    // }
    // readLUT();
    //
    // flutetree = flute(d, x, y, ACCURACY);
    // printf("FLUTE wirelength = %d\n", flutetree.length);
    // // Print input points
    // printf("\n----\n");
    // printTree(flutetree);
    // const int MAX_POINT = 100;
    // int steiner[MAX_POINT];
    // int pin[MAX_POINT];
    // int steiner_cnt = 0;
    // for (int i = 0; i < 2 * d - 2; i++) {
    //     int is_steiner = 1;
    //     for (int j = 0; j < d; j++) {
    //         if (x[j] == flutetree.branch[i].x && y[j] == flutetree.branch[i].y) {
    //             is_steiner = 0;
    //             break;
    //         }
    //
    //     }
    //     if (is_steiner) {
    //         steiner[steiner_cnt++] = i;
    //     } else {
    //         pin[i - steiner_cnt] = i;
    //     }
    // }
    // if (steiner_cnt != d - 2) {
    //     printf("Steiner Count Incorrect(!=d-2)\n");
    // }
    // for (int i = 0; i < steiner_cnt; i++) {
    //     printf("%d ", steiner[i]);
    // }
    // printf("\n----\n");
    // for (int i = 0; i < 2 * d - 2 - steiner_cnt; i++) {
    //     printf("%d ", pin[i]);
    // }
    // printf("\n----\n");

    // flutewl = flute_wl(d, x, y, ACCURACY);
    // printf("FLUTE wirelength (without RSMT construction) = %d\n", flutewl);
}

/***********************************************************
	Sum_ProductによるLDPC符号の画像シミュレータ　統合版(2014.11.14)並木、堂浦

	tanh型 Shuffled BP Sum-Productシミュレータ(2014.11.4)

	Bit serial Sum-Productアルゴリズムシミュレータ(2004.08.18)を改変　by並木
***********************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#include <ctype.h> //堂浦

#include "random.h"
#include "process_time.h"



#define snr 3.0			// Eb/N0[dB]の値
#define max_iteration 5	// 最大復号繰り返し回数
#define iteration_image 1	// 画像出力する繰り返し回数
#define gazo_pattern 1		// 0: 画像を分割する　1:画像をまとめる 
#define seed 1				// 乱数の種
#define simulation 0		// 0:ノイズ付与
#define decode 1			// 0:shuffledBP 1:sum product (復号法の指定)
#define encoding 1			// all 0 の時 encoding=0, not all 0 の時 encoding=1
#define stop_condition 0	// 0:誤りビット数指定　1:誤りブロック数指定（可変時に利用）
//#define target_blocks 100	// 指定する誤りブロック数（可変時に利用）
//#define target_bits	100		// 指定する誤りビット数（可変時に利用）

#define bmp_file "lena256_mono.bmp"	// 読み込む画像ファイル名(4の倍数のデータを入れること)
#define infile	"504.252H.txt"	// 読み込む検査行列ファイル名
//#define infile	"816_408.txt"
//#define infile	"arrange_504.txt"
//#define infile	"result2_1008.txt"
#define infile2 "504.252G.txt"	// 読み込む生成行列ファイル名
//#define infile3 ""				// 読み込む符号語ファイル名
//#define infile4 ""				// 読み込むエラーファイル名
#define outfile	"result_simulation_progress.csv"
#define outfile2 "result_simulation.csv"
// 出力するBER特性のファイル名



#pragma warning ( disable : 4996 )// "warning C4996: 'fopen' が古い形式として宣言されました。"の出力からの除去

/***********************************************************
		グローバル変数
***********************************************************/

/*検査行列用(復号)パラメータ*/
int N;				// 検査行列の列数
int M;				// 検査行列の行数
double R;			// 符号化率
int col_max;		// 列重みの最大値
int row_max;		// 行重みの最大値
int *col_weight;	// 各列の列重み
int *row_weight;	// 各行の行重み
int **A;			// Ｈのｍ行目の列インデックス集合Ａ
int **B;			// Ｈのｎ列目の行インデックス集合Ｂ

/*生成行列用パラメータ*/
int GN;                         // 生成行列の列数
int GM;                         // 生成行列の行数
int Gcol_max;           // 列重みの最大値
int Grow_max;           // 行重みの最大値
int *Gcol_weight;       // 各列の列重み
int *Grow_weight;       // 各行の行重み
int **GA;                       // Gのｍ行目の列インデックス集合Ａ
int **GB;                       // Gのｎ列目の行インデックス集合Ｂ

int **info_seq;              // 情報系列
int *syndrome;              // シンドローム系列

int *codeword;		// 符号語
double *noise;		// 雑音系列
double *rword;		// 受信語
double *LLR;		// 対数尤度比
int *order;			// 復号対象ビット
double **r;			// τ
double **ip;		// ε
double **z;			// z
double *total_ipusiron;// 総外部情報
int *temp_bit;		// 一時推定語
//double snr;			// Eb/N0[dB]
double channel_var;	// 雑音の分散
int total_blocks;	// 送信符号語数（可変時に利用）
int total_bits;		// 送信ビット数（可変時に利用）
int error_blocks;	// 復号後の誤りブロック数
int error_bits;		// 復号後の誤りビット数
int undecoded_error_blocks;	// 復号前の誤りブロック数
int undecoded_error_bits;	// 復号前の誤りビット数
//int *iteration_error;	// 繰り返し毎の誤りビット数
int syndrome_check;				// 復号成功のチェック
int syndrome_error_ite_count;	// パリティチェック失敗時の繰り返し回数
int syndrome_error_bits;			// パリティチェック失敗時の誤りビット数
int syndrome_error_blocks;		// パリティチェック失敗時の誤りブロック数

int ***temp_bit_map;			//一時推定語の保存
int CN;							//ループ用繰り返し回数
int iteration_number;			//出力する画像の数

int **decoding_image;			//復号の画像情報
int **decoding_ex_image;		//復号の差分画像情報
int code_number;				//送信符号語数

int count;						//カウント
int ite_count;					//繰り返し回数
int *count_error;				//エラーカウント
int gazosize;					//画像の情報ビット数
int tate;						//画像の縦の大きさ
int yoko;						//画像の横の大きさ

unsigned char *head;			// 画像のヘッダ
unsigned char *pic;				// 画像情報
int *digital_pic;				// 画像の0,1情報

/***********************************************************
		検査行列ファイルの読み込み
***********************************************************/
void read_MacKay_format(){

	int i,n,m,temp;
	FILE *fp;

	if((fp = fopen(infile,"r"))==NULL){		// 検査行列ファイル(MacKayフォーマット)を開く
		fprintf(stderr,"Can't open infile\n");
		exit(-1);
	}

	fscanf(fp,"%d %d\n",&N,&M);				// 列数Ｎ、行数Ｍ読み込み
	fscanf(fp,"%d %d\n",&col_max,&row_max);	// 列重み、行重みの最大値を読み込む

	R = (double)(N-M)/N;					// 符号化率の計算

	col_weight = (int *)malloc(sizeof(int)*N);		// 列重み用の領域確保
	for(n = 0; n < N; n++)
		fscanf(fp,"%d",&col_weight[n]);		// ｎ列目の列重みを読み込む

	row_weight = (int *)malloc(sizeof(int)*M);		// 行重み用の領域確保	
	for(m = 0; m < M; m++)
		fscanf(fp,"%d",&row_weight[m]);		// ｍ行目の行重みを読み込む

	B = (int **)malloc(sizeof(int*)*N);
	for(n = 0; n < N; n++)
		B[n] = (int *)malloc(sizeof(int)*col_weight[n]);// Ｈのｎ列目の行インデックス集合Ｂの領域確保

	A = (int **)malloc(sizeof(int*)*M);
	for(m = 0; m < M; m++)
		A[m] = (int *)malloc(sizeof(int)*row_weight[m]);// Ｈのｍ行目の列インデックス集合Ａの領域確保

	for(n = 0; n < N; n++){
		for(i = 0; i < col_weight[n]; i++){
			fscanf(fp,"%d",&temp);
			if(temp!=0){// ｎ列目の行インデックス集合Ｂを読み込む
				B[n][i] = temp-1;
			}else{
				while(temp==0){
					fscanf(fp,"%d",&temp);
				}
				B[n][i] = temp-1;
			}
			// Ｃ言語の配列は０番目からなので１引く
		}
	}
	for(m = 0; m < M; m++){
		for(i = 0; i < row_weight[m]; i++){
			fscanf(fp,"%d",&temp);			// ｍ行目の列インデックス集合Ａを読み込む
			if(temp!=0){
				A[m][i] = temp-1;
			}else{
				while(temp==0){
					fscanf(fp,"%d",&temp);
				}
				A[m][i] = temp-1;
			}// Ｃ言語の配列は０番目からなので１引く
		}
	}

	//ここから生成行列読み込み
    if((fp = fopen(infile2,"r"))==NULL){            // 生成行列ファイル(MacKayフォーマット)を開く
		fprintf(stderr,"Can't open infile\n");
        exit(-1);
    }
                                                                                                                                              
    fscanf(fp,"%d %d\n",&GN,&GM);                   // 列数Ｎ、行数Ｍ読み込み
    fscanf(fp,"%d %d\n",&Gcol_max,&Grow_max);       // 列重み、行重みの最大値を読み込む
                                                                                                                                              
    Gcol_weight = (int *)malloc(sizeof(int)*GN);           // 列重み用の領域確保
	for(n = 0; n < GN; n++)
		fscanf(fp,"%d",&Gcol_weight[n]);                // ｎ列目の列重みを読み込む

	Grow_weight = (int *)malloc(sizeof(int)*GM);           // 行重み用の領域確保
    for(m = 0; m < GM; m++)
		fscanf(fp,"%d",&Grow_weight[m]);                // ｍ行目の行重みを読み込む
                                                                                                                                              
    GB = (int **)malloc(sizeof(int*)*GN);
	for(n = 0; n < GN; n++)
		GB[n] = (int *)malloc(sizeof(int)*Gcol_weight[n]);// Gのｎ列目の行インデックス集合Ｂの領域確保
                                                                                                                                              
	GA = (int **)malloc(sizeof(int*)*GM);
	for(m = 0; m < GM; m++)
		GA[m] = (int *)malloc(sizeof(int)*Grow_weight[m]);// Gのｍ行目の列インデックス集合Ａの領域確保

	for(n = 0; n < GN; n++){
		for(i = 0; i < Gcol_max; i++){
			fscanf(fp,"%d",&temp);                  // ｎ列目の行インデックス集合Ｂを読み込む
			if(i < Gcol_weight[n]){
				if(temp!=0){
					GB[n][i] = temp-1;
				}/*else{
					while(temp==0){
						fscanf(fp,"%d",&temp);
					}
					GB[n][i] = temp-1;
				}// Ｃ言語の配列は０番目からなので１引く*/
			}
		}
	}
                                                                                                                                              
	for(m = 0; m < GM; m++){
		for(i = 0; i < Grow_max; i++){
			fscanf(fp,"%d",&temp);                  // ｍ行目の列インデックス集合Ａを読み込む
			if(i < Grow_weight[m]){
				if(temp!=0){
					GA[m][i] = temp-1;
				}/*else{
					while(temp==0){
						fscanf(fp,"%d",&temp);
					}
					GA[m][i] = temp-1;
				}// Ｃ言語の配列は０番目からなので１引く*/
			}
		}
	}

	fclose(fp);								// 検査行列ファイル(MacKayフォーマット)を閉じる
}
/***********************************************************
		画像読み込み
***********************************************************/
void load_image(){

	int i,j,tmp,size;
	FILE *fp;
	/*
	unsigned char *buf;
	unsigned char wid[21];
	unsigned char hei[25];
	int height =0; //とりあえずの値
	int x, y;
	int count=0; //RGB3バイト分の読み込みをカウント
	unsigned char lum[800][800]={0};  //輝度分布行列(0行,0列は使わない) 初期値0
	unsigned char r,g,b;
	int zero = 4 - (width *3) % 4; //4バイトの整数倍になるように埋める0の数
	*/
	if((fp = fopen(bmp_file, "rb" ))== NULL ){
		printf("Can't open1\n");
		getchar();
		exit(-1);
	}
	/*
	size = fread( buf, sizeof( unsigned char ), 1000000, fp ); //ファイルサイズ(byte)
	rewind(fp);
	*/
	tate = 0;
	yoko = 0;
	head = (unsigned char *)malloc(54); //適当に場所とり
	fread( head, sizeof( unsigned char ), 54, fp ); //ヘッダ部取得(unsigned char 0~255)
	yoko+=head[18];
	tate+=head[22];
	yoko+=head[19]*256;
	tate+=head[23]*256;
//	tate+=head[20]*256*256;		// 大きいデータを入れないように
//	yoko+=head[24]*256*256;
//	tate+=head[21]*256*256*256;
//	yoko+=head[25]*256*256*256;
	gazosize=tate*yoko*24;
	size=tate*yoko*3;
	
//	printf("%d %d\n",tate,yoko);
	pic = (unsigned char *)malloc(size); //適当に場所とり
	fread( pic, sizeof( unsigned char ), size, fp );//輝度値部取得(unsigned char 0~255)
	rewind(fp);

	if((digital_pic = (int *)malloc(sizeof(int)*(gazosize))) == NULL){
		fprintf(stderr,"Can't allocate memory\n");
		exit(-1);
    }
	for(i=0;i<gazosize;i++){
		for(j=0;j<size;j++){
			tmp=pic[j];
			digital_pic[i]=tmp/128;
			tmp-=digital_pic[i]*128;
			i++;
			digital_pic[i]=tmp/64;
			tmp-=digital_pic[i]*64;
			i++;
			digital_pic[i]=tmp/32;
			tmp-=digital_pic[i]*32;
			i++;
			digital_pic[i]=tmp/16;
			tmp-=digital_pic[i]*16;
			i++;
			digital_pic[i]=tmp/8;
			tmp-=digital_pic[i]*8;
			i++;
			digital_pic[i]=tmp/4;
			tmp-=digital_pic[i]*4;
			i++;
			digital_pic[i]=tmp/2;
			tmp-=digital_pic[i]*2;
			i++;
			digital_pic[i]=tmp;
			i++;
		}
	}
	/*
	for( i=54; height>0; i++ ){//ヘッダ部は無視
		if(count==0){
			r = buf[i];//Rの輝度値
		}
		if(count==1){
			g = buf[i];//Gの輝度値
		}
		if(count==2){
			b = buf[i];//Bの輝度値
			lum[height][j]=0.298912*r+0.586611*g+0.114478*b;
		}
		count++;
		if(count==3){
			j++;//次のピクセルへ移動
			count = 0; //カウント初期化
		}
		if(j > width){// 画像の右端まで読み込む　終わったら　上の段へ
			switch(zero){//0の数だけオフセットを飛ばす
				case 0:
					break;
				case 1:
					i= i+1;
					break;
				case 2:
					i= i+2;
					break;
				case 3:
					i =i+3;
					break;
			}
			height--;//上の段へ移動
			j = 1; //見るピクセルを左端へもどす
		}
	}*/
  //確認出力
  /*
  for( num=0; num<54; num++ ){
		printf("%3d ",head[num]);
		if((num+1)%16==0 && num !=0){
			printf("\n");
		}
  }
  printf("\n");
  printf("\n");
  
  for( num=0; num<size-54; num++ ){
		printf("%3d ",pic[num]);
		if((num+1)%16==0 && num !=0){
			printf("\n");
		}
  }
  */
	free(pic);
	fclose( fp );
}
/***********************************************************
		
***********************************************************/
void printf_image_bitmap(){
	int n,x,i,k,j;
	FILE *fp;
	char filename[100];
	unsigned char *tmp;
	
//			printf("A\n");
	if((tmp = (unsigned char *)malloc(1)) == NULL){
		fprintf(stderr,"Can't allocate memory\n");
		exit(-1);
    }
//			printf("A\n");
	for(n=1;n<iteration_number;n++){
		if((k=(n-1)*iteration_image) > max_iteration) k = max_iteration;
		sprintf(filename,"iteration%d.bmp",k);
		if((fp = fopen(filename,"wb")) == NULL){	// 画像出力ファイルを開く
			fprintf(stderr,"Can't open\n");
			exit(-1);
		}
		fwrite(head,sizeof(unsigned char),54,fp);
//			printf("A\n");
		for(i=0;i<gazosize;i++){
//			printf("A\n");
			tmp[0]=0;
//			printf("B\n");
			tmp[0]+=decoding_image[n][i]*128;
			i++;
			tmp[0]+=decoding_image[n][i]*64;
			i++;
			tmp[0]+=decoding_image[n][i]*32;
			i++;
			tmp[0]+=decoding_image[n][i]*16;
			i++;
			tmp[0]+=decoding_image[n][i]*8;
			i++;
			tmp[0]+=decoding_image[n][i]*4;
			i++;
			tmp[0]+=decoding_image[n][i]*2;
			i++;
			tmp[0]+=decoding_image[n][i];
			fwrite(tmp,sizeof(unsigned char),1,fp);
		}
	fclose(fp);
	}
	
	for(n=1;n<iteration_number;n++){
		if((k=(n-1)*iteration_image) > max_iteration) k = max_iteration;
		sprintf(filename,"ex_iteration%d.bmp",k);
		if((fp = fopen(filename,"wb")) == NULL){	// 画像出力ファイルを開く
			fprintf(stderr,"Can't open\n");
			exit(-1);
		}
		fwrite(head,sizeof(unsigned char),54,fp);
		for(i=0;i<gazosize;i++){
			tmp[0]=0;
			tmp[0]+=decoding_ex_image[n][i]*128;
			i++;
			tmp[0]+=decoding_ex_image[n][i]*64;
			i++;
			tmp[0]+=decoding_ex_image[n][i]*32;
			i++;
			tmp[0]+=decoding_ex_image[n][i]*16;
			i++;
			tmp[0]+=decoding_ex_image[n][i]*8;
			i++;
			tmp[0]+=decoding_ex_image[n][i]*4;
			i++;
			tmp[0]+=decoding_ex_image[n][i]*2;
			i++;
			tmp[0]+=decoding_ex_image[n][i];
			fwrite(tmp,sizeof(unsigned char),1,fp);
		}
		fclose(fp);
	}
	if(gazo_pattern == 1){
		x=yoko*2;
//		printf("%d\n",x);
//		head[21]=x/256/256/256;
//		x-=head[21]*256*256*256;
		head[20]=x/256/256;
		x-=head[20]*256*256;
//		printf("%d\n",x);
		head[19]=x/256;
		x-=head[19]*256;
//		printf("%d\n",x);
		head[18]=x;
		x=tate*iteration_number;
//		head[25]=x/256/256/256;
//		x-=head[25]*256*256/256;
//		printf("%d\n",x);
		head[24]=x/256/256;
		x-=head[24]*256*256;
//		printf("%d\n",x);
		head[23]=x/256;
		x-=head[23]*256;
//		printf("%d\n",x);
		head[22]=x;
		x=tate*iteration_number*yoko*2*3;
//		printf("%d\n",x);
		x+=54;
		head[5]=x/256/256/256;
		x-=head[5]*256*256*256;
//		printf("%d\n",x);
		head[4]=x/256/256;
		x-=head[4]*256*256;
//		printf("%d\n",x);
		head[3]=x/256;
		x-=head[3]*256;
//		printf("%d\n",x);
		head[2]=x;
		sprintf(filename,"iteration%d_max%d.bmp",iteration_image,max_iteration);
		if((fp = fopen(filename,"wb")) == NULL){	// 画像出力ファイルを開く
		fprintf(stderr,"Can't open\n");
			exit(-1);
		}
		fwrite(head,sizeof(unsigned char),54,fp);
		for(n=iteration_number-1;n>=0;n--){
			i=0;
			while(i<gazosize){
				for(j=0;j<yoko*3;j++){
					tmp[0]=0;
					tmp[0]+=decoding_image[n][i]*128;
					i++;
					tmp[0]+=decoding_image[n][i]*64;
					i++;
					tmp[0]+=decoding_image[n][i]*32;
					i++;
					tmp[0]+=decoding_image[n][i]*16;
					i++;
					tmp[0]+=decoding_image[n][i]*8;
					i++;
					tmp[0]+=decoding_image[n][i]*4;
					i++;
					tmp[0]+=decoding_image[n][i]*2;
					i++;
					tmp[0]+=decoding_image[n][i];
					i++;
					fwrite(tmp,sizeof(unsigned char),1,fp);
				}
				i-=yoko*24;
				for(j=0;j<yoko*3;j++){
					tmp[0]=0;
					tmp[0]+=decoding_ex_image[n][i]*128;
					i++;
					tmp[0]+=decoding_ex_image[n][i]*64;
					i++;
					tmp[0]+=decoding_ex_image[n][i]*32;
					i++;
					tmp[0]+=decoding_ex_image[n][i]*16;
					i++;
					tmp[0]+=decoding_ex_image[n][i]*8;
					i++;
					tmp[0]+=decoding_ex_image[n][i]*4;
					i++;
					tmp[0]+=decoding_ex_image[n][i]*2;
					i++;
					tmp[0]+=decoding_ex_image[n][i];
					i++;
					fwrite(tmp,sizeof(unsigned char),1,fp);
				}
			}
//			printf("%d\n",n);
		}
		fclose(fp);
	}
	free(tmp);
}
/***********************************************************
		
***********************************************************/
/*
int cast_bin(int size,int size_bin, unsigned char pic[], int img_bin[]){
	int i=0;
	int j=0;
	for(i=0; i<size_bin; i++){
		for(j=0; j<size; j++){
			int tmp = pic[j];
			img_bin[i] = tmp/128;
			if(img_bin[i] ==1){
				tmp-=128;
			}
			i++;
			
			img_bin[i] = tmp/64;
			if(img_bin[i] ==1){
				tmp-=64;
			}
			i++;
			
			img_bin[i] = tmp/32;
			if(img_bin[i] ==1){
				tmp-=32;
			}
			i++;
			
			img_bin[i] = tmp/16;
			if(img_bin[i] ==1){
				tmp-=16;
			}
			i++;

			img_bin[i] = tmp/8;
			if(img_bin[i] ==1){
				tmp-=8;
			}
			i++;
			
			img_bin[i] = tmp/4;
			if(img_bin[i] ==1){
				tmp-=4;
			}
			i++;

			img_bin[i] = tmp/2;
			if(img_bin[i] ==1){
				tmp-=2;
			}
			i++;

			img_bin[i] = tmp;
			i++;
		}
	}

	for( i=0; i<size_bin; i++ ){
		printf("%d",img_bin[i]);
		if((i+1)%8==0 && i !=0){
			printf("\n");

		}
	}

		return 0;
}
*/
/***********************************************************
		
***********************************************************/
/*
int pic_load_bin(int img_bin[]){

	
	unsigned char *image,*head; //(0~255)でヘッダと輝度値を配列に
	int size;
	//(0,1)で輝度値を配列に

	image = (unsigned char *)malloc(66000);
	head = (unsigned char *)malloc(66000);
	//img_bin = (int *)malloc(10000000);

	size = pic_load(head,image);//ヘッダと輝度値を取得 (0~255) 返り値はファイルサイズ


	cast_bin(size, (size-54)*8, image, img_bin);


	return head[18]*head[22]*3*8;
}
*/
/***********************************************************
		シミュレーションパラメータの出力
***********************************************************/
/*
void print_parameter(){

	time_t t;			// 時間用変数
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
    time(&t);

	// ファイルに出力
	fprintf(fp,"#\n");
	fprintf(fp,"# %s",ctime(&t));
	fprintf(fp,"# %s  code_length = %d  row_weight = %d  col_weight = %d  R = %1.4f\n",
		infile,N,row_max,col_max,R);
	fprintf(fp,"# seed = %d\n",seed);
	fprintf(fp,"# max_iteration = %d\n",max_iteration);
	fprintf(fp,"# simulation = %d\n",simulation);
	if(simulation == 2)
		fprintf(fp,"# stop_condition = %d  target_blocks = %d  target_bits = %d\n",stop_condition,target_blocks,target_bits);
	else
		fprintf(fp,"# code_number = %d\n",code_number);
	fprintf(fp,"\n");
	fclose(fp);

	// 画面に出力
	printf("%s",ctime(&t));
	printf("%s  code_length = %d  row_weight = %d  col_weight = %d  R = %1.4f\n",
		infile,N,row_max,col_max,R);
	printf("seed = %d\n",seed);
	printf("max_iteration = %d\n",max_iteration);
	printf("simulation = %d\n",simulation);
	if(simulation == 2)
		printf("stop_condition = %d  target_blocks = %d  target_bits = %d\n",stop_condition,target_blocks,target_bits);
	else
		printf("code_number = %d\n",code_number);
	printf("\n");
}*/
/*
・データを取った年月日
・符号について（構成法、符号長、行重み、列重み、符号化率）
・乱数の種（時間でなく固定にする？）
・最大繰り返し回数
・閾値について（スタート、動作）
・ビット誤り率、フレーム誤り率
*/
/***********************************************************
		シミュレーションパラメータの出力 csv形式
***********************************************************/
void print_parameter_csv(){

	time_t t;			// 時間用変数
	FILE *fp;

	if((fp = fopen(outfile2,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile2\n");
		exit(-1);
	}
    time(&t);

	// ファイルに出力
	fprintf(fp,"#tanh shuffled BP\n");
	fprintf(fp,"#%s,",ctime(&t));
	fprintf(fp,"#%s,code_length = %d,row_weight = %d,col_weight = %d,R = %1.4f\n",
		infile,N,row_max,col_max,R);
	fprintf(fp,"#seed = %d\n",seed);
	fprintf(fp,"#max_iteration = %d\n",max_iteration);
	fprintf(fp,"#simulation = %d\n",simulation);
	fprintf(fp,"#code_number = %d\n",code_number);
	fprintf(fp,"\n");
	fprintf(fp,"SNR,BER,BERse,BERnse,undecoded_BER,iteration,parity_error_iteration_rate,parity_error_rate,undecoded_error_bit,err_bits,");
	fprintf(fp,"parity_error_bits,not_parity_error_bits,block_errer_rate,undecoded_error_blocks,error_blocks,parity_error_blocks,not_parity_error_blocks\n");
	//パリティエラーが無い時parity_error_iteration_rateは0/0=nan
	fclose(fp);

	// 画面に出力
	printf("%s",ctime(&t));
	printf("%s  code_length = %d  row_weight = %d  col_weight = %d  R = %1.4f\n",
		infile,N,row_max,col_max,R);
	printf("seed = %d\n",seed);
	printf("max_iteration = %d\n",max_iteration);
	printf("simulation = %d\n",simulation);
	printf("code_number = %d\n",code_number);
	printf("\n");

/*
・データを取った年月日
・符号について（構成法、符号長、行重み、列重み、符号化率）
・乱数の種（時間でなく固定にする？）
・最大繰り返し回数
・閾値について（スタート、動作）
・ビット誤り率、フレーム誤り率
*/
}
/***********************************************************
		必要な領域の確保
***********************************************************/
void get_memory(){

	int m,n;

	code_number = (gazosize) / (N-M);
	
	if((gazosize) % (N-M) > 0){
		code_number++;
	}

	iteration_number=max_iteration/iteration_image;
	n = max_iteration%iteration_image;
	if(n > 0){
		iteration_number++;
	}
	iteration_number+=2;

	if((info_seq = (int **)malloc(sizeof(int*)*(code_number))) == NULL){
		fprintf(stderr,"1Can't allocate memory\n");
		exit(-1);
    }
	for(n = 0; n < code_number;n++){
		if((info_seq[n] = (int *)malloc(sizeof(int)*(N-M))) == NULL){// 情報系列の領域確保 (N-M):符号長-検査語数=情報長
			fprintf(stderr,"2Can't allocate memory\n");
			exit(-1);
	    }
	}
	if((syndrome = (int *)malloc(sizeof(int)*M)) == NULL){// syndrome系列の領域確保
		fprintf(stderr,"3Can't allocate memory\n");
		exit(-1);
    }
	if((codeword = (int *)malloc(sizeof(int)*N)) == NULL){// 符号語の領域確保
		fprintf(stderr,"4Can't allocate memory\n");
		exit(-1);
	}
	if((noise = (double *)malloc(sizeof(double)*N)) == NULL){// 雑音系列の領域確保
		fprintf(stderr,"5Can't allocate memory\n");
		exit(-1);
	}
	if((rword = (double *)malloc(sizeof(double)*N)) == NULL){// 受信語の領域確保
		fprintf(stderr,"6Can't allocate memory\n");
		exit(-1);
	}
	if((LLR = (double *)malloc(sizeof(double)*N)) == NULL){// 対数尤度比の領域確保
		fprintf(stderr,"7Can't allocate memory\n");
		exit(-1);
	}
	if((order = (int *)malloc(sizeof(double)*N)) == NULL){// 復号対象ビットの領域確保
		fprintf(stderr,"8Can't allocate memory\n");
		exit(-1);
	}
	if((r = (double **)malloc(sizeof(double*)*N)) == NULL){
		fprintf(stderr,"9Can't allocate memory\n");
		exit(-1);
	}
    for(n = 0; n < N; n++){
		if((r[n] = (double *)malloc(sizeof(double)*col_max)) == NULL){// 対数外部値比αの領域確保
			fprintf(stderr,"10Can't allocate memory\n");
			exit(-1);
		}
	}
	if((ip = (double **)malloc(sizeof(double*)*N)) == NULL){
		fprintf(stderr,"11Can't allocate memory\n");
		exit(-1);
	}
    for(n = 0; n < N; n++){
		if((ip[n] = (double *)malloc(sizeof(double)*col_max)) == NULL){// 対数外部値比εの領域確保
			fprintf(stderr,"12Can't allocate memory\n");
			exit(-1);
		}
	}
	if((z = (double **)malloc(sizeof(double*)*M)) == NULL){
		fprintf(stderr,"13Can't allocate memory\n");
		exit(-1);
	}
    for(m = 0; m < M; m++){
		if((z[m] = (double *)malloc(sizeof(double)*row_max)) == NULL){// 対数事前値比βの領域確保
			fprintf(stderr,"14Can't allocate memory\n");
			exit(-1);
		}
	}
	if((total_ipusiron = (double *)malloc(sizeof(double)*N)) == NULL){// 総外部情報の領域確保
		fprintf(stderr,"15Can't allocate memory\n");
		exit(-1);
	}
	if((temp_bit = (int *)malloc(sizeof(int)*N)) == NULL){// 一時推定語の領域確保
		fprintf(stderr,"16Can't allocate memory\n");
		exit(-1);
	}

	if((temp_bit_map = (int ***)malloc(sizeof(int**)*iteration_number)) == NULL){
		fprintf(stderr,"17Can't allocate memory\n");
		exit(-1);
	}
	for(n = 0; n < iteration_number ;n++){
		if((temp_bit_map[n] = (int **)malloc(sizeof(int*)*(code_number))) == NULL){
			fprintf(stderr,"18Can't allocate memory\n");
			exit(-1);
	    }
	}
	for(n = 0; n < iteration_number;n++){
		for(m = 0; m < code_number;m++){
			if((temp_bit_map[n][m] = (int *)malloc(sizeof(int)*(N))) == NULL){
				fprintf(stderr,"19Can't allocate memory\n");
				exit(-1);
			}
	    }
	}
	if((decoding_image = (int **)malloc(sizeof(int*)*iteration_number)) == NULL){
		fprintf(stderr,"20Can't allocate memory\n");
		exit(-1);
	}
	for(n = 0; n < iteration_number;n++){
		if((decoding_image[n] = (int *)malloc(sizeof(int)*(gazosize))) == NULL){
			fprintf(stderr,"21Can't allocate memory\n");
			exit(-1);
	    }
	}
	if((decoding_ex_image = (int **)malloc(sizeof(int*)*iteration_number)) == NULL){
		fprintf(stderr,"22Can't allocate memory\n");
		exit(-1);
	}

	

	for(n = 0; n < iteration_number;n++){
		if((decoding_ex_image[n] = (int *)malloc(sizeof(int)*(code_number*(N-M)))) == NULL){
			fprintf(stderr,"23Can't allocate memory\n");
			exit(-1);
	    }
	}
//	if((iteration_error = (int *)malloc(sizeof(int)*max_iteration)) == NULL){// 繰り返し毎の誤りビット数の領域確保
//		fprintf(stderr,"24Can't allocate memory\n");
//		exit(-1);
//	}
	if((count_error = (int *)malloc(sizeof(int)*N)) == NULL){// 繰り返し毎の誤りビット数の領域確保
		fprintf(stderr,"25Can't allocate memory\n");
		exit(-1);
	}
}

/***********************************************************
                符号語作成
************************************************************/
void encode(){
                                                                                                                                              
	int i,j;
                                                                                                                                              
	for(i = 0; i < GN; i++){    //codewordの初期化
		codeword[i] = 0;
	}

	for(i = 0; i < GN; i++){
		
        for(j = 0; j < Gcol_weight[i]; j++){
			codeword[i] ^= info_seq[CN][GB[i][j]];        //符号語の作成
        }
		/*
		if(count==0){
			printf("%d\n",codeword[i]);
		}*/
		
	}
	count++;
	/*
	for(i=0;i<GN;i++){
		printf("%d",codeword[i]);
	}
	printf("\n");
	*/
}
/***********************************************************
                情報系列作成
************************************************************/
void mk_info(){
}
/***********************************************************
                情報系列作成
************************************************************/
void image_mk_info(){
                                                                                                                                              
	int i,m,n;
	int k;
	i=0;
	n=0;
	
	for(k = 0; k < gazosize; k++){
		info_seq[n][i] = digital_pic[k];   //ランダムな情報系列を作る
//		printf("%d",digital_pic[k]);
		i++;
		if(i==N-M){
			n++;
			i=0;
//	printf("a\n");
		}
		
	}
	while(n<code_number){
		info_seq[n][i]=0;
//		printf("0");
		i++;
		if(i==N-M){
			n++;
			i=0;
		}
	}
//	printf("aaa\n");
}

/***********************************************************
		受信語作成
***********************************************************/
void make_received_word(){

	int n;
	double sigma;

	init_mrnd( rand() );			// rand() の部分は乱数の種
	init_gaussd(_init[7], _func[7], rand());

	channel_var = 1.0 / (2.0 * R * pow(10.0,snr/10.0));	// 雑音の分散
	sigma = sqrt(channel_var);	// 雑音の標準偏差

	for(n = 0; n < N; n++){
		noise[n] = gaussd(0,sigma);		// 平均と標準偏差に対応した雑音作成
		rword[n] = 1.0 - 2.0*codeword[n] + noise[n];	// BPSK変調後に雑音を加えて受信語作成
	}
	/*for(n = 50; n < 250; n++){//消失
		rword[n]=0;
	}*/
	

}
/***********************************************************
		対数尤度比を出力
***********************************************************/
/*
void print_LLR(){

	int n;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
	fprintf(fp,"#LLR\n");
	n=0;
	for(n = 0; n < N; n++){
		fprintf(fp,"%d,",LLR[n]);
	}
	fprintf(fp,"\n");
	fclose(fp);
	}
	*/
/***********************************************************
		符号語を出力
***********************************************************/
void print_codeword(){

	int n;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
	fprintf(fp,"#codeword\n");
	n=0;
	for(n = 0; n < N; n++){
		fprintf(fp,"%d,",codeword[n]);
	}
	fprintf(fp,"\n");
	fclose(fp);
	}
/***********************************************************
		復号前の誤りビット数、誤りブロック数を数える
***********************************************************/
void undecoded_error_count(){

	int n,error=0;

	for(n = 0; n < N; n++){	// 硬判定復号を行う
		if(rword[n] >= 0.0)
			temp_bit[n] = 0;
		else
			temp_bit[n] = 1;
	}

	if(encoding == 0){	// all 0 の時
		for(n = 0; n < N; n++)
			error += temp_bit[n];	// 誤りビット数を数える
	}
	else{	// not all 0 の時
		for(n = 0; n < N; n++)
			error += temp_bit[n] ^ codeword[n];	// 誤りビット数を数える
	}

	if(error > 0){		// 復号前の誤りビット数、誤りブロック数を更新
		undecoded_error_blocks++;
		undecoded_error_bits += error;
	}


}

/***********************************************************
		対数尤度比計算
***********************************************************/
void get_LLR(){

	int n;

	for(n = 0; n < N; n++){
		LLR[n] = 2.0 * rword[n] / channel_var;
	}
}

/***********************************************************
		sign関数
***********************************************************/
int sign(double x){

	if(x >= 0.0)
		return 1;
	else
		return -1;
}

/***********************************************************
		εのf関数
***********************************************************/
double ipusiron(double x){

	double f;
	double a = x;
	if(a >=0.99999){
		return 12.21;
	}
	if(a <= -0.99999){
		return -12.21;
	}
	f = log((a+1.0)/(1.0-a));
	return f;
}

/***********************************************************
		temp_bit_mapの初期化
***********************************************************/
void init_temp_bit_map(){

	int m,i,k;
	k=0;
	for (i=0; i<iteration_number;i++){
		for(m=0;m<N;m++){
			temp_bit_map[i][CN][m]=codeword[m];
		}
	}
	for(m=0;m<N;m++){
		if(rword[m] >= 0.0){
			temp_bit_map[1][CN][m]=0;
		}else{
			temp_bit_map[1][CN][m]=1;
		}
	}
}
/***********************************************************
		temp_bit_mapを情報系列に戻す
***********************************************************/
void unit_temp_bit(){

	int m,n,i,k,kk;
	for (i=0; i<iteration_number;i++){
		k=0;
		kk=0;
		for(n=0;n<code_number;n++){
			for(m=0;m<N;m++){
				if(m >= N-M && k<gazosize ){
					decoding_image[i][k]=temp_bit_map[i][n][m];
					k++;
				}
				if(m < N-M){
					decoding_ex_image[i][kk]=temp_bit_map[i][n][m];
					kk++;
				}
			}
		}
	}
}
/***********************************************************
		Shuffled BP Sum-Product復号法の初期化
***********************************************************/
void init_Shuffled_BP_Sum_Product(){

	int m,n,i;

	get_LLR();		// 対数尤度比計算
	for(m = 0; m < M; m++){
		for(i = 0; i < row_weight[m]; i++){
			z[m][i] = LLR[A[m][i]];	// 対数事前値比βの初期化	(m行目i番目の要素を表す)
		}
	}
	for(n = 0; n < N; n++){
		order[n] = n;	// 復号する順序を設定(bit_serialだから0～N-1)
	}
}
/***********************************************************
		外部値と事前値を出力
***********************************************************/
/*
void print_alpha_beta(){

	int i,j,n,m;
	int morder[N];
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
	fprintf(fp,"#alpha\n");
	n=0;
	m=0;
	for(i=0;i<N;i++){
		morder[i]=0;
	}
	for(i = 0; i < M; i++){
		for(j = 0; j < N; j++){
			if(A[m][n] == j){
				fprintf(fp,"%1.5f,",r[j][morder[j]]);
				morder[j]++;
				n++;
			}else{
				fprintf(fp,"0,");
			}
		}
		fprintf(fp,"\n");
		m++;
		n=0;
	}
	fprintf(fp,"#beta\n");
	m=0;
	for(i = 0; i < M; i++){
		for(j = 0; j < N; j++){
			if(A[m][n] == j){
				fprintf(fp,"%1.5f,",z[m][n]);
				if(n < row_weight[i]){
					n++;
				}
			}else{
				fprintf(fp,"0,");
			}
		}
		n=0;
		fprintf(fp,"\n");
		m++;
	}
	m=0;
	fclose(fp);
	}*/
/***********************************************************
		推定語を出力
***********************************************************/
/*
void print_tempbit(){

	int i;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
	fprintf(fp,"#temp_bit\n");
	for(i = 0; i < N; i++){
		fprintf(fp,"%d,",temp_bit[i]);
	}
	fprintf(fp,"\n");
	fclose(fp);
	}
	*/
/***********************************************************
		tanh Shuffled BP Sum-Product復号法
***********************************************************/
void tanh_Shuffled_BP_Sum_Product(){

	int i,j,n,iteration,count,ite;
	double sum,prod;

	// Step 1: 初期化（初期値代入、対数尤度比計算）
	init_Shuffled_BP_Sum_Product();
	ite=1;
	//繰り返し復号ここから
	for(iteration = 0; iteration < max_iteration; iteration++){
		// Step 2: 行処理
		for(n = 0; n < N; n++){
			sum = LLR[order[n]];
			for(i = 0; i < col_weight[order[n]]; i++){		// order[n]列目i番目のrを求める
				prod = 1.0;// αを求める際に必要な積の初期化
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i] ][j] != order[n]){	// B[order[n]][i]行目j番目の列インデックスがorder[n]でないとき
//						temp = LLR[A[B[order[n]][i]][j]] + beta[ B[order[n]][i] ][j];
//						sum += Gallager_f( fabs(temp) );	// tempの絶対値を足し合わせていく
//						prod *= sign(temp);					// tempの符合を掛け合わる
						prod *= tanh(z[B[order[n]][i]][j] / 2.0);
					}
				}
				r[order[n]][i] = prod;// * Gallager_f(sum);	// order[n]列目i番目のr
				ip[order[n]][i] = ipusiron(prod);// order[n]列目i番目のε
				sum += ip[order[n]][i];
			}
			// Step 3: 列処理
//			sum = 0.0;			// βを求める際に必要な和の初期化
//			for(i = 0; i < col_weight[order[n]]; i++){
//				sum += ip[order[n]][i];		// order[n]列目の対数外部値比を足し合わせていく
//			}
//			sum += LLR[order[n]];
			total_ipusiron[order[n]] = sum;		// n列目の総外部情報を求める
			for(i = 0; i < col_weight[order[n]]; i++){
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i]][j] == order[n]){	// B[order[n]][i]行目j番目の列インデックスがnのとき
						z[B[order[n]][i]][j] = total_ipusiron[order[n]] - ip[order[n]][i];	// B[order[n]][i]行目j番目の対数事前値比βを更新
					}							// (総外部情報から自分の対数外部値比を引く)
				}
			}
		}
		// Step 4: 終了判定
		for(n = 0; n < N; n++){		// 一時推定語を求める
			if(sign(total_ipusiron[n]) == 1)
				temp_bit[n] = 0;
			else
				temp_bit[n] = 1;
		}
		count = 0;		// 終了条件を満たすかどうか調べるための変数
		for(i = 0; i < M; i++){	
			syndrome[i] = 0;
			for(j = 0; j < row_weight[i]; j++){
				syndrome[i] ^= temp_bit[A[i][j]];
			}
			if(syndrome[i] == 1){
				count++;
			}
		}
		n = (iteration+1)%iteration_image;
		if(n == 0){
			ite++;
			for(n = 0; n < N; n++){		// 一時推定語の保存
				temp_bit_map[ite][CN][n]=temp_bit[n];
			}
		}
		if(count == 0){
			ite_count += iteration+1;
			syndrome_check = iteration+1;
			break;	// 復号に成功
		}

	}
	if(count != 0){
		ite_count += max_iteration;
	}
		//繰り返し復号ここまで
}
/***********************************************************
		tanh Sum-Product復号法
***********************************************************/
void tanh_Sum_Product(){

	int i,j,n,iteration,count,ite;
	double sum,prod;

	// Step 1: 初期化（初期値代入、対数尤度比計算）
	init_Shuffled_BP_Sum_Product();
	ite=1;
	//繰り返し復号ここから
	for(iteration = 0; iteration < max_iteration; iteration++){
		// Step 2: 行処理
		for(n = 0; n < N; n++){
			for(i = 0; i < col_weight[order[n]]; i++){		// order[n]列目i番目のrを求める
				prod = 1.0;// αを求める際に必要な積の初期化
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i] ][j] != order[n]){	// B[order[n]][i]行目j番目の列インデックスがorder[n]でないとき
//						temp = LLR[A[B[order[n]][i]][j]] + beta[ B[order[n]][i] ][j];
//						sum += Gallager_f( fabs(temp) );	// tempの絶対値を足し合わせていく
//						prod *= sign(temp);					// tempの符合を掛け合わる
						prod *= tanh(z[B[order[n]][i]][j] / 2.0);
					}
				}
				r[order[n]][i] = prod;// * Gallager_f(sum);	// order[n]列目i番目のr
				ip[order[n]][i] = ipusiron(prod);// order[n]列目i番目のε
			}
		}
		for(n = 0; n < N; n++){
			// Step 3: 列処理
			sum = 0.0;			// βを求める際に必要な和の初期化
			for(i = 0; i < col_weight[order[n]]; i++){
				sum += ip[order[n]][i];		// order[n]列目の対数外部値比を足し合わせていく
			}
			sum += LLR[order[n]];
			total_ipusiron[order[n]] = sum;		// n列目の総外部情報を求める
			for(i = 0; i < col_weight[order[n]]; i++){
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i]][j] == order[n]){	// B[order[n]][i]行目j番目の列インデックスがnのとき
						z[B[order[n]][i]][j] = total_ipusiron[order[n]] - ip[order[n]][i];	// B[order[n]][i]行目j番目の対数事前値比βを更新
					}							// (総外部情報から自分の対数外部値比を引く)
				}
			}
		}
		// Step 4: 終了判定
		for(n = 0; n < N; n++){		// 一時推定語を求める
			if(sign(total_ipusiron[n]) == 1)
				temp_bit[n] = 0;
			else
				temp_bit[n] = 1;
		}
		count = 0;		// 終了条件を満たすかどうか調べるための変数
		for(i = 0; i < M; i++){	
			syndrome[i] = 0;
			for(j = 0; j < row_weight[i]; j++){
				syndrome[i] ^= temp_bit[A[i][j]];
			}
			if(syndrome[i] == 1){
				count++;
			}
		}
		n = (iteration+1)%iteration_image;
		if(n == 0){
			ite++;
			for(n = 0; n < N; n++){		// 一時推定語の保存
				temp_bit_map[ite][CN][n]=temp_bit[n];
			}
		}
		if(count == 0){
			ite_count += iteration+1;
			syndrome_check = iteration+1;
			break;	// 復号に成功
		}

	}
	if(count != 0){
		ite_count += max_iteration;
	}
		//繰り返し復号ここまで
}
/***********************************************************
		復号後の誤りビット数、誤りブロック数を数える
***********************************************************/
void error_count(){

	int n,error=0;

	if(encoding == 0){	// all 0 の時
		for(n = 0; n < N; n++){
			count_error[n] += temp_bit[n];
			error += temp_bit[n];	// 誤りビット数を数える
		}
	}
	else{	// not all 0 の時
		for(n = 0; n < N; n++)
			error += temp_bit[n] ^ codeword[n];	// 誤りビット数を数える
	}

	if(error > 0){		// 復号後の誤りビット数、誤りブロック数を更新
		error_blocks++;						//復号失敗時の誤りブロック数を更新
		error_bits += error;			//復号失敗時の誤りビット数を更新
		if(syndrome_check != 0){
			syndrome_error_blocks++;		//パリティチェック失敗時のエラーブロック数更新
			syndrome_error_bits += error;	//パリティチェック失敗時のエラービット更新
			syndrome_error_ite_count += syndrome_check;	//パリティチェック失敗時の繰り返し回数更新
		}
	}
}
/***********************************************************
		結果の出力
***********************************************************/
/*
void print_result(){

	int i;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
	if(simulation == 1){
		fprintf(fp,"##snr = %1.2f ##BER = %1.12f ##undecoded_BER = %1.12f ##iteration_rate = %1.8f  ##undecoded_error_bits = %d/%d  error_bits = %d/%d  %1.1f  %1.8f  undecoded_error_blocks = %d/%d  error_blocks = %d/%d\n",
			snr,(double)error_bits / (double)(code_number*N),(double)undecoded_error_bits / (double)(code_number*N),ite_count*1.0/code_number, undecoded_error_bits,code_number*N,error_bits,code_number*N,
			snr,(double)error_blocks / (double)(code_number),undecoded_error_blocks,code_number,error_blocks,code_number);
		fclose(fp);
	}
	else if(simulation == 2){
		fprintf(fp,"%1.1f  %1.8f  ##undecoded_error_bits = %d/%d  error_bits = %d/%d  %1.1f  %1.8f  undecoded_error_blocks = %d/%d  error_blocks = %d/%d\n",
			snr,(double)error_bits / (double)total_bits,undecoded_error_bits,total_bits,error_bits,total_bits,
			snr,(double)error_blocks / (double)total_blocks,undecoded_error_blocks,total_blocks,error_blocks,total_blocks);
		fclose(fp);
	}
	else if(simulation == 3){
	}
	else if(simulation == 4){
		for(i = 0; i < max_iteration; i++)
			fprintf(fp,"%d  %1.8f\n",i+1,(double)iteration_error[i] / (double)(code_number*N));
		fclose(fp);
	}
}
*/
/***********************************************************
		結果の出力 csv形式
***********************************************************/
void print_result_csv(){

	int i;
	FILE *fp;

	if((fp = fopen(outfile2,"a")) == NULL){	// BER出力ファイルを開く
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
	fprintf(fp,"%1.2f,%1.12f,%1.12f,%1.12f,%1.12f,",
		snr,(double)(error_bits) / (double)(code_number*N),(double)(syndrome_error_bits) / (double)(code_number*N),
		(double)(error_bits-syndrome_error_bits) / (double)(code_number*N),(double)undecoded_error_bits / (double)(code_number*N));
	fprintf(fp,"%1.8f,%1.8f,%1.8f,%d,%d,%d,%d,%1.8f,%d,%d,%d,%d\n",
		ite_count*1.0,(double)(syndrome_error_ite_count)/(double)(syndrome_error_blocks),(double)(syndrome_error_blocks) / (double)(code_number),undecoded_error_bits,
		error_bits,syndrome_error_bits,(error_bits-syndrome_error_bits),(double)(error_blocks) / (double)(code_number),
		undecoded_error_blocks,error_blocks,syndrome_error_blocks,(error_blocks-syndrome_error_blocks));
	fclose(fp);
}
/***********************************************************
		送信符号語数を固定してのシミュレーション
***********************************************************/
/*void simulation_loop1(){

	int n,code,parcent=0;

	process_counter_start();		//プロセスカウンタstart
	printf("進行状況\n");
	for(snr = min_snr; snr <= max_snr; snr += snr_interval){
		undecoded_error_blocks = 0;	// 復号前の誤りブロック数初期化
		undecoded_error_bits = 0;	// 復号前の誤りビット数初期化
		error_blocks = 0;	// 復号後の誤りブロック数初期化
		error_bits = 0;		// 復号後の誤りビット数初期化
		ite_count = 0;
		for(n = 0; n < N; n++){
			count_error[n] = 0;
		}
		for(code = 0; code < code_number; code++){
			parcent++;
			printf("%4.2f％\r",(parcent) / (code_number * ((max_snr-min_snr)/snr_interval+1.0)) * 100);
			if(encoding == 0){	// all 0 の時
				for(n = 0; n < N; n++)
					codeword[n] = 0;	// 符号語作成
			}
			else{				// not all 0 の時
				mk_info();
				encode();
			}
			make_received_word();	// 受信語作成
			undecoded_error_count();	// 復号前の誤りビット数、誤りブロック数を数える
			Shuffled_BP_Sum_Product();	// Bit Serial Sum-Product復号法
			error_count();		// 復号後の誤りビット数、誤りブロック数を数える
		}
		print_result();		// 結果の出力
	}
	process_counter_finish("finish");	// プロセスカウンタfinish
}*/
/***********************************************************
		csv形式imageシミュレーション
***********************************************************/
void simulation_loop(){

	int n;
	int i,j;
//	printf("progress\n");
	process_counter_start();		///プロセスカウンタstart
	image_mk_info();				// 画像情報を符号化できる大きさに分割する
	
//	printf("progress2\n");
	for(CN = 0; CN < code_number; CN++){
		undecoded_error_blocks = 0;	// 復号前の誤りブロック数初期化
		undecoded_error_bits = 0;	// 復号前の誤りビット数初期化
		error_blocks = 0;	// 復号後の誤りブロック数初期化
		error_bits = 0;		// 復号後の誤りビット数初期化
		ite_count = 0;		// 復号後の繰り返し回数初期化
		syndrome_error_ite_count = 0;	// パリティチェック失敗時の繰り返し回数初期化
		syndrome_error_bits = 0;		// パリティチェック失敗時の誤りビット数初期化
		syndrome_error_blocks = 0;		// パリティチェック失敗時の誤りブロック数初期化
		for(n = 0; n < N; n++){
			count_error[n] = 0;
		}
//		parcent++;
//		printf("%4.2fpersent\r",(parcent) / (code_number * ((max_snr-min_snr)/snr_interval+1.0)) * 100);
		/*
		if(encoding == 0){	// all 0 の時
			for(n = 0; n < N; n++){
				codeword[n] = 0;	// 符号語作成
			}
		}else{				// not all 0 の時
			mk_info();
			encode();
		}
		*/
//		printf("A\n");
		mk_info();
		encode();
//		printf("A\n");
		syndrome_check = 0;		// パリティチェック監視関数初期化
//		print_codeword();
		make_received_word();	// 受信語作成
//		printf("A\n");
		init_temp_bit_map();	//tempbitの初期化
//		printf("A\n");
		undecoded_error_count();	// 復号前の誤りビット数、誤りブロック数を数える
//		print_codeword();
		if(decode==0){
			tanh_Shuffled_BP_Sum_Product();	// Bit Serial Sum-Product復号法
		}else if(decode==1){
			tanh_Sum_Product();
		}
//		printf("A\n");
//		print_tempbit();
		error_count();		// 復号後の誤りビット数、誤りブロック数を数える
//		print_result_csv();		// 結果の出力
	}
	unit_temp_bit();				// 分割した符号を統合する
	/*
		printf("B\n");
	for(i=0;i<iteration_number;i++){
		for(j=0;j<gazosize;j++){
			printf("%d",decoding_image[i][j]);
			if(decoding_ex_image[i][j] != 0 && decoding_ex_image[i][j] != 1){
				printf("\n%d %d\n",i,j);
			}
		}
		printf("C\n");
	}*/

	printf_image_bitmap();

	process_counter_finish("finish");	// プロセスカウンタfinish
}


/***********************************************************
		送信符号語数を可変してのシミュレーション
***********************************************************/
/*void simulation_loop2(){

	int n;

	for(snr = min_snr; snr <= max_snr; snr += snr_interval){
		total_blocks = 0;	// 送信符号語数初期化
		total_bits = 0;		// 送信ビット数初期化
		undecoded_error_blocks = 0;	// 復号前の誤りブロック数初期化
		undecoded_error_bits = 0;	// 復号前の誤りビット数初期化
		error_blocks = 0;	// 復号後の誤りブロック数初期化
		error_bits = 0;		// 復号後の誤りビット数初期化
		while(1){	// 終了条件を満たすまでループ
			total_blocks++;		// 送信符号語数更新
			total_bits += N;	// 送信ビット数更新

			if(encoding == 0){	// all 0 の時
				for(n = 0; n < N; n++)
					codeword[n] = 0;	// 符号語作成
			}
			else{				// not all 0 の時
				mk_info();
				encode();
			}
			make_received_word();	// 受信語作成
			undecoded_error_count();	// 復号前の誤りビット数、誤りブロック数を数える
			Shuffled_BP_Sum_Product();	// Bit Serial Sum-Product復号法
			error_count();		// 復号後の誤りビット数、誤りブロック数を数える
			if((error_bits >= target_bits) && (stop_condition == 0))	// 指定した誤りビット数に達したらbreak
				break;
			if((error_blocks >= target_blocks) && (stop_condition == 1))	// 指定した誤りブロック数に達したらbreak
				break;
			if(total_blocks == code_number)	// 最大送信符号語数に達したらbreak
				break;
		}
		print_result();		// 結果の出力
	}
}
*/
/***********************************************************
		SN比、送信符号語数を指定してのシミュレーション
***********************************************************/
/*void simulation_loop3(){
}*/

/***********************************************************
		繰り返し毎に誤り率を計算するシミュレーション
***********************************************************/
/*void simulation_loop4(){

	int i,n,code,parcent=0;

	process_counter_start();		// プロセスカウンタstart 
	printf("進行状況\n");
	for(snr = min_snr; snr <= max_snr; snr += snr_interval){
		for(i = 0; i < max_iteration; i++)
			iteration_error[i] = 0;	// 繰り返し回数毎の誤りビット数初期化
		for(code = 0; code < code_number; code++){
			parcent++;
			printf("%4.2f％\r",(double)parcent / (double)code_number * 100);
			if(encoding == 0){	// all 0 の時
				for(n = 0; n < N; n++)
					codeword[n] = 0;	// 符号語作成
			}
			else{				// not all 0 の時
				mk_info();
				encode();
			}
			make_received_word();	// 受信語作成
			Shuffled_BP_Sum_Product();		// Sum-Product復号法
		}
		print_result();		// 結果の出力
	}
	process_counter_finish("finish");	// プロセスカウンタfinish
}*/


/***********************************************************
		確保した領域の開放
***********************************************************/
void free_memory(){

	free(col_weight);	// 各列の列重み
	free(row_weight);	// 各行の行重み
	free(A);			// Ｈのｍ行目の列インデックス集合Ａ
	free(B);			// Ｈのｎ列目の行インデックス集合Ｂ
	free(Gcol_weight);       // 各列の列重み
    free(Grow_weight);       // 各行の行重み
    free(GA);           // Gのｍ行目の列インデックス集合Ａ
    free(GB);           // Gのｎ列目の行インデックス集合Ｂ
	free(codeword);		// 符号語
	free(noise);		// 雑音系列
	free(rword);		// 受信語
	free(LLR);			// 対数尤度比
	free(r);			// τ
	free(ip);			// ε
	free(z);			// z
	free(total_ipusiron);	// 総外部情報
	free(temp_bit);		// 一時推定語
	/*
	free(iteration_error);	// 繰り返し回数毎の誤りビット数
	free(count_error);
	*/
	free(info_seq);
	free(syndrome);
	free(temp_bit_map);
	free(decoding_ex_image);
	free(decoding_image);
	free(head);
	free(digital_pic);
	
}


/***********************************************************
		main関数
***********************************************************/
int main(){

	srand((unsigned int)time(NULL));		// 乱数の種
	
	count = 0;
	

	read_MacKay_format();	// 検査行列ファイルの読み込み
	load_image();			// 画像ファイルの読み込み
	print_parameter_csv();	// csvシミュレーションパラメータの出力
	get_memory();			// 必要な領域の確保
	simulation_loop();
	free_memory();			// 確保した領域の開放

	return 0;
}
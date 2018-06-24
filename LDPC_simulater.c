/***********************************************************
	Sum_Product�ɂ��LDPC�����̉摜�V�~�����[�^�@������(2014.11.14)���؁A���Y

	tanh�^ Shuffled BP Sum-Product�V�~�����[�^(2014.11.4)

	Bit serial Sum-Product�A���S���Y���V�~�����[�^(2004.08.18)�����ρ@by����
***********************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#include <ctype.h> //���Y

#include "random.h"
#include "process_time.h"



#define snr 3.0			// Eb/N0[dB]�̒l
#define max_iteration 5	// �ő啜���J��Ԃ���
#define iteration_image 1	// �摜�o�͂���J��Ԃ���
#define gazo_pattern 1		// 0: �摜�𕪊�����@1:�摜���܂Ƃ߂� 
#define seed 1				// �����̎�
#define simulation 0		// 0:�m�C�Y�t�^
#define decode 1			// 0:shuffledBP 1:sum product (�����@�̎w��)
#define encoding 1			// all 0 �̎� encoding=0, not all 0 �̎� encoding=1
#define stop_condition 0	// 0:���r�b�g���w��@1:���u���b�N���w��i�ώ��ɗ��p�j
//#define target_blocks 100	// �w�肷����u���b�N���i�ώ��ɗ��p�j
//#define target_bits	100		// �w�肷����r�b�g���i�ώ��ɗ��p�j

#define bmp_file "lena256_mono.bmp"	// �ǂݍ��މ摜�t�@�C����(4�̔{���̃f�[�^�����邱��)
#define infile	"504.252H.txt"	// �ǂݍ��ތ����s��t�@�C����
//#define infile	"816_408.txt"
//#define infile	"arrange_504.txt"
//#define infile	"result2_1008.txt"
#define infile2 "504.252G.txt"	// �ǂݍ��ސ����s��t�@�C����
//#define infile3 ""				// �ǂݍ��ޕ�����t�@�C����
//#define infile4 ""				// �ǂݍ��ރG���[�t�@�C����
#define outfile	"result_simulation_progress.csv"
#define outfile2 "result_simulation.csv"
// �o�͂���BER�����̃t�@�C����



#pragma warning ( disable : 4996 )// "warning C4996: 'fopen' ���Â��`���Ƃ��Đ錾����܂����B"�̏o�͂���̏���

/***********************************************************
		�O���[�o���ϐ�
***********************************************************/

/*�����s��p(����)�p�����[�^*/
int N;				// �����s��̗�
int M;				// �����s��̍s��
double R;			// ��������
int col_max;		// ��d�݂̍ő�l
int row_max;		// �s�d�݂̍ő�l
int *col_weight;	// �e��̗�d��
int *row_weight;	// �e�s�̍s�d��
int **A;			// �g�̂��s�ڂ̗�C���f�b�N�X�W���`
int **B;			// �g�̂���ڂ̍s�C���f�b�N�X�W���a

/*�����s��p�p�����[�^*/
int GN;                         // �����s��̗�
int GM;                         // �����s��̍s��
int Gcol_max;           // ��d�݂̍ő�l
int Grow_max;           // �s�d�݂̍ő�l
int *Gcol_weight;       // �e��̗�d��
int *Grow_weight;       // �e�s�̍s�d��
int **GA;                       // G�̂��s�ڂ̗�C���f�b�N�X�W���`
int **GB;                       // G�̂���ڂ̍s�C���f�b�N�X�W���a

int **info_seq;              // ���n��
int *syndrome;              // �V���h���[���n��

int *codeword;		// ������
double *noise;		// �G���n��
double *rword;		// ��M��
double *LLR;		// �ΐ��ޓx��
int *order;			// �����Ώۃr�b�g
double **r;			// ��
double **ip;		// ��
double **z;			// z
double *total_ipusiron;// ���O�����
int *temp_bit;		// �ꎞ�����
//double snr;			// Eb/N0[dB]
double channel_var;	// �G���̕��U
int total_blocks;	// ���M�����ꐔ�i�ώ��ɗ��p�j
int total_bits;		// ���M�r�b�g���i�ώ��ɗ��p�j
int error_blocks;	// ������̌��u���b�N��
int error_bits;		// ������̌��r�b�g��
int undecoded_error_blocks;	// �����O�̌��u���b�N��
int undecoded_error_bits;	// �����O�̌��r�b�g��
//int *iteration_error;	// �J��Ԃ����̌��r�b�g��
int syndrome_check;				// ���������̃`�F�b�N
int syndrome_error_ite_count;	// �p���e�B�`�F�b�N���s���̌J��Ԃ���
int syndrome_error_bits;			// �p���e�B�`�F�b�N���s���̌��r�b�g��
int syndrome_error_blocks;		// �p���e�B�`�F�b�N���s���̌��u���b�N��

int ***temp_bit_map;			//�ꎞ�����̕ۑ�
int CN;							//���[�v�p�J��Ԃ���
int iteration_number;			//�o�͂���摜�̐�

int **decoding_image;			//�����̉摜���
int **decoding_ex_image;		//�����̍����摜���
int code_number;				//���M�����ꐔ

int count;						//�J�E���g
int ite_count;					//�J��Ԃ���
int *count_error;				//�G���[�J�E���g
int gazosize;					//�摜�̏��r�b�g��
int tate;						//�摜�̏c�̑傫��
int yoko;						//�摜�̉��̑傫��

unsigned char *head;			// �摜�̃w�b�_
unsigned char *pic;				// �摜���
int *digital_pic;				// �摜��0,1���

/***********************************************************
		�����s��t�@�C���̓ǂݍ���
***********************************************************/
void read_MacKay_format(){

	int i,n,m,temp;
	FILE *fp;

	if((fp = fopen(infile,"r"))==NULL){		// �����s��t�@�C��(MacKay�t�H�[�}�b�g)���J��
		fprintf(stderr,"Can't open infile\n");
		exit(-1);
	}

	fscanf(fp,"%d %d\n",&N,&M);				// �񐔂m�A�s���l�ǂݍ���
	fscanf(fp,"%d %d\n",&col_max,&row_max);	// ��d�݁A�s�d�݂̍ő�l��ǂݍ���

	R = (double)(N-M)/N;					// ���������̌v�Z

	col_weight = (int *)malloc(sizeof(int)*N);		// ��d�ݗp�̗̈�m��
	for(n = 0; n < N; n++)
		fscanf(fp,"%d",&col_weight[n]);		// ����ڂ̗�d�݂�ǂݍ���

	row_weight = (int *)malloc(sizeof(int)*M);		// �s�d�ݗp�̗̈�m��	
	for(m = 0; m < M; m++)
		fscanf(fp,"%d",&row_weight[m]);		// ���s�ڂ̍s�d�݂�ǂݍ���

	B = (int **)malloc(sizeof(int*)*N);
	for(n = 0; n < N; n++)
		B[n] = (int *)malloc(sizeof(int)*col_weight[n]);// �g�̂���ڂ̍s�C���f�b�N�X�W���a�̗̈�m��

	A = (int **)malloc(sizeof(int*)*M);
	for(m = 0; m < M; m++)
		A[m] = (int *)malloc(sizeof(int)*row_weight[m]);// �g�̂��s�ڂ̗�C���f�b�N�X�W���`�̗̈�m��

	for(n = 0; n < N; n++){
		for(i = 0; i < col_weight[n]; i++){
			fscanf(fp,"%d",&temp);
			if(temp!=0){// ����ڂ̍s�C���f�b�N�X�W���a��ǂݍ���
				B[n][i] = temp-1;
			}else{
				while(temp==0){
					fscanf(fp,"%d",&temp);
				}
				B[n][i] = temp-1;
			}
			// �b����̔z��͂O�Ԗڂ���Ȃ̂łP����
		}
	}
	for(m = 0; m < M; m++){
		for(i = 0; i < row_weight[m]; i++){
			fscanf(fp,"%d",&temp);			// ���s�ڂ̗�C���f�b�N�X�W���`��ǂݍ���
			if(temp!=0){
				A[m][i] = temp-1;
			}else{
				while(temp==0){
					fscanf(fp,"%d",&temp);
				}
				A[m][i] = temp-1;
			}// �b����̔z��͂O�Ԗڂ���Ȃ̂łP����
		}
	}

	//�������琶���s��ǂݍ���
    if((fp = fopen(infile2,"r"))==NULL){            // �����s��t�@�C��(MacKay�t�H�[�}�b�g)���J��
		fprintf(stderr,"Can't open infile\n");
        exit(-1);
    }
                                                                                                                                              
    fscanf(fp,"%d %d\n",&GN,&GM);                   // �񐔂m�A�s���l�ǂݍ���
    fscanf(fp,"%d %d\n",&Gcol_max,&Grow_max);       // ��d�݁A�s�d�݂̍ő�l��ǂݍ���
                                                                                                                                              
    Gcol_weight = (int *)malloc(sizeof(int)*GN);           // ��d�ݗp�̗̈�m��
	for(n = 0; n < GN; n++)
		fscanf(fp,"%d",&Gcol_weight[n]);                // ����ڂ̗�d�݂�ǂݍ���

	Grow_weight = (int *)malloc(sizeof(int)*GM);           // �s�d�ݗp�̗̈�m��
    for(m = 0; m < GM; m++)
		fscanf(fp,"%d",&Grow_weight[m]);                // ���s�ڂ̍s�d�݂�ǂݍ���
                                                                                                                                              
    GB = (int **)malloc(sizeof(int*)*GN);
	for(n = 0; n < GN; n++)
		GB[n] = (int *)malloc(sizeof(int)*Gcol_weight[n]);// G�̂���ڂ̍s�C���f�b�N�X�W���a�̗̈�m��
                                                                                                                                              
	GA = (int **)malloc(sizeof(int*)*GM);
	for(m = 0; m < GM; m++)
		GA[m] = (int *)malloc(sizeof(int)*Grow_weight[m]);// G�̂��s�ڂ̗�C���f�b�N�X�W���`�̗̈�m��

	for(n = 0; n < GN; n++){
		for(i = 0; i < Gcol_max; i++){
			fscanf(fp,"%d",&temp);                  // ����ڂ̍s�C���f�b�N�X�W���a��ǂݍ���
			if(i < Gcol_weight[n]){
				if(temp!=0){
					GB[n][i] = temp-1;
				}/*else{
					while(temp==0){
						fscanf(fp,"%d",&temp);
					}
					GB[n][i] = temp-1;
				}// �b����̔z��͂O�Ԗڂ���Ȃ̂łP����*/
			}
		}
	}
                                                                                                                                              
	for(m = 0; m < GM; m++){
		for(i = 0; i < Grow_max; i++){
			fscanf(fp,"%d",&temp);                  // ���s�ڂ̗�C���f�b�N�X�W���`��ǂݍ���
			if(i < Grow_weight[m]){
				if(temp!=0){
					GA[m][i] = temp-1;
				}/*else{
					while(temp==0){
						fscanf(fp,"%d",&temp);
					}
					GA[m][i] = temp-1;
				}// �b����̔z��͂O�Ԗڂ���Ȃ̂łP����*/
			}
		}
	}

	fclose(fp);								// �����s��t�@�C��(MacKay�t�H�[�}�b�g)�����
}
/***********************************************************
		�摜�ǂݍ���
***********************************************************/
void load_image(){

	int i,j,tmp,size;
	FILE *fp;
	/*
	unsigned char *buf;
	unsigned char wid[21];
	unsigned char hei[25];
	int height =0; //�Ƃ肠�����̒l
	int x, y;
	int count=0; //RGB3�o�C�g���̓ǂݍ��݂��J�E���g
	unsigned char lum[800][800]={0};  //�P�x���z�s��(0�s,0��͎g��Ȃ�) �����l0
	unsigned char r,g,b;
	int zero = 4 - (width *3) % 4; //4�o�C�g�̐����{�ɂȂ�悤�ɖ��߂�0�̐�
	*/
	if((fp = fopen(bmp_file, "rb" ))== NULL ){
		printf("Can't open1\n");
		getchar();
		exit(-1);
	}
	/*
	size = fread( buf, sizeof( unsigned char ), 1000000, fp ); //�t�@�C���T�C�Y(byte)
	rewind(fp);
	*/
	tate = 0;
	yoko = 0;
	head = (unsigned char *)malloc(54); //�K���ɏꏊ�Ƃ�
	fread( head, sizeof( unsigned char ), 54, fp ); //�w�b�_���擾(unsigned char 0~255)
	yoko+=head[18];
	tate+=head[22];
	yoko+=head[19]*256;
	tate+=head[23]*256;
//	tate+=head[20]*256*256;		// �傫���f�[�^�����Ȃ��悤��
//	yoko+=head[24]*256*256;
//	tate+=head[21]*256*256*256;
//	yoko+=head[25]*256*256*256;
	gazosize=tate*yoko*24;
	size=tate*yoko*3;
	
//	printf("%d %d\n",tate,yoko);
	pic = (unsigned char *)malloc(size); //�K���ɏꏊ�Ƃ�
	fread( pic, sizeof( unsigned char ), size, fp );//�P�x�l���擾(unsigned char 0~255)
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
	for( i=54; height>0; i++ ){//�w�b�_���͖���
		if(count==0){
			r = buf[i];//R�̋P�x�l
		}
		if(count==1){
			g = buf[i];//G�̋P�x�l
		}
		if(count==2){
			b = buf[i];//B�̋P�x�l
			lum[height][j]=0.298912*r+0.586611*g+0.114478*b;
		}
		count++;
		if(count==3){
			j++;//���̃s�N�Z���ֈړ�
			count = 0; //�J�E���g������
		}
		if(j > width){// �摜�̉E�[�܂œǂݍ��ށ@�I�������@��̒i��
			switch(zero){//0�̐������I�t�Z�b�g���΂�
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
			height--;//��̒i�ֈړ�
			j = 1; //����s�N�Z�������[�ւ��ǂ�
		}
	}*/
  //�m�F�o��
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
		if((fp = fopen(filename,"wb")) == NULL){	// �摜�o�̓t�@�C�����J��
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
		if((fp = fopen(filename,"wb")) == NULL){	// �摜�o�̓t�@�C�����J��
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
		if((fp = fopen(filename,"wb")) == NULL){	// �摜�o�̓t�@�C�����J��
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

	
	unsigned char *image,*head; //(0~255)�Ńw�b�_�ƋP�x�l��z���
	int size;
	//(0,1)�ŋP�x�l��z���

	image = (unsigned char *)malloc(66000);
	head = (unsigned char *)malloc(66000);
	//img_bin = (int *)malloc(10000000);

	size = pic_load(head,image);//�w�b�_�ƋP�x�l���擾 (0~255) �Ԃ�l�̓t�@�C���T�C�Y


	cast_bin(size, (size-54)*8, image, img_bin);


	return head[18]*head[22]*3*8;
}
*/
/***********************************************************
		�V�~�����[�V�����p�����[�^�̏o��
***********************************************************/
/*
void print_parameter(){

	time_t t;			// ���ԗp�ϐ�
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER�o�̓t�@�C�����J��
		fprintf(stderr,"Can't open outfile\n");
		exit(-1);
	}
    time(&t);

	// �t�@�C���ɏo��
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

	// ��ʂɏo��
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
�E�f�[�^��������N����
�E�����ɂ��āi�\���@�A�������A�s�d�݁A��d�݁A���������j
�E�����̎�i���ԂłȂ��Œ�ɂ���H�j
�E�ő�J��Ԃ���
�E臒l�ɂ��āi�X�^�[�g�A����j
�E�r�b�g��藦�A�t���[����藦
*/
/***********************************************************
		�V�~�����[�V�����p�����[�^�̏o�� csv�`��
***********************************************************/
void print_parameter_csv(){

	time_t t;			// ���ԗp�ϐ�
	FILE *fp;

	if((fp = fopen(outfile2,"a")) == NULL){	// BER�o�̓t�@�C�����J��
		fprintf(stderr,"Can't open outfile2\n");
		exit(-1);
	}
    time(&t);

	// �t�@�C���ɏo��
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
	//�p���e�B�G���[��������parity_error_iteration_rate��0/0=nan
	fclose(fp);

	// ��ʂɏo��
	printf("%s",ctime(&t));
	printf("%s  code_length = %d  row_weight = %d  col_weight = %d  R = %1.4f\n",
		infile,N,row_max,col_max,R);
	printf("seed = %d\n",seed);
	printf("max_iteration = %d\n",max_iteration);
	printf("simulation = %d\n",simulation);
	printf("code_number = %d\n",code_number);
	printf("\n");

/*
�E�f�[�^��������N����
�E�����ɂ��āi�\���@�A�������A�s�d�݁A��d�݁A���������j
�E�����̎�i���ԂłȂ��Œ�ɂ���H�j
�E�ő�J��Ԃ���
�E臒l�ɂ��āi�X�^�[�g�A����j
�E�r�b�g��藦�A�t���[����藦
*/
}
/***********************************************************
		�K�v�ȗ̈�̊m��
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
		if((info_seq[n] = (int *)malloc(sizeof(int)*(N-M))) == NULL){// ���n��̗̈�m�� (N-M):������-�����ꐔ=���
			fprintf(stderr,"2Can't allocate memory\n");
			exit(-1);
	    }
	}
	if((syndrome = (int *)malloc(sizeof(int)*M)) == NULL){// syndrome�n��̗̈�m��
		fprintf(stderr,"3Can't allocate memory\n");
		exit(-1);
    }
	if((codeword = (int *)malloc(sizeof(int)*N)) == NULL){// ������̗̈�m��
		fprintf(stderr,"4Can't allocate memory\n");
		exit(-1);
	}
	if((noise = (double *)malloc(sizeof(double)*N)) == NULL){// �G���n��̗̈�m��
		fprintf(stderr,"5Can't allocate memory\n");
		exit(-1);
	}
	if((rword = (double *)malloc(sizeof(double)*N)) == NULL){// ��M��̗̈�m��
		fprintf(stderr,"6Can't allocate memory\n");
		exit(-1);
	}
	if((LLR = (double *)malloc(sizeof(double)*N)) == NULL){// �ΐ��ޓx��̗̈�m��
		fprintf(stderr,"7Can't allocate memory\n");
		exit(-1);
	}
	if((order = (int *)malloc(sizeof(double)*N)) == NULL){// �����Ώۃr�b�g�̗̈�m��
		fprintf(stderr,"8Can't allocate memory\n");
		exit(-1);
	}
	if((r = (double **)malloc(sizeof(double*)*N)) == NULL){
		fprintf(stderr,"9Can't allocate memory\n");
		exit(-1);
	}
    for(n = 0; n < N; n++){
		if((r[n] = (double *)malloc(sizeof(double)*col_max)) == NULL){// �ΐ��O���l�䃿�̗̈�m��
			fprintf(stderr,"10Can't allocate memory\n");
			exit(-1);
		}
	}
	if((ip = (double **)malloc(sizeof(double*)*N)) == NULL){
		fprintf(stderr,"11Can't allocate memory\n");
		exit(-1);
	}
    for(n = 0; n < N; n++){
		if((ip[n] = (double *)malloc(sizeof(double)*col_max)) == NULL){// �ΐ��O���l��Â̗̈�m��
			fprintf(stderr,"12Can't allocate memory\n");
			exit(-1);
		}
	}
	if((z = (double **)malloc(sizeof(double*)*M)) == NULL){
		fprintf(stderr,"13Can't allocate memory\n");
		exit(-1);
	}
    for(m = 0; m < M; m++){
		if((z[m] = (double *)malloc(sizeof(double)*row_max)) == NULL){// �ΐ����O�l����̗̈�m��
			fprintf(stderr,"14Can't allocate memory\n");
			exit(-1);
		}
	}
	if((total_ipusiron = (double *)malloc(sizeof(double)*N)) == NULL){// ���O�����̗̈�m��
		fprintf(stderr,"15Can't allocate memory\n");
		exit(-1);
	}
	if((temp_bit = (int *)malloc(sizeof(int)*N)) == NULL){// �ꎞ�����̗̈�m��
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
//	if((iteration_error = (int *)malloc(sizeof(int)*max_iteration)) == NULL){// �J��Ԃ����̌��r�b�g���̗̈�m��
//		fprintf(stderr,"24Can't allocate memory\n");
//		exit(-1);
//	}
	if((count_error = (int *)malloc(sizeof(int)*N)) == NULL){// �J��Ԃ����̌��r�b�g���̗̈�m��
		fprintf(stderr,"25Can't allocate memory\n");
		exit(-1);
	}
}

/***********************************************************
                ������쐬
************************************************************/
void encode(){
                                                                                                                                              
	int i,j;
                                                                                                                                              
	for(i = 0; i < GN; i++){    //codeword�̏�����
		codeword[i] = 0;
	}

	for(i = 0; i < GN; i++){
		
        for(j = 0; j < Gcol_weight[i]; j++){
			codeword[i] ^= info_seq[CN][GB[i][j]];        //������̍쐬
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
                ���n��쐬
************************************************************/
void mk_info(){
}
/***********************************************************
                ���n��쐬
************************************************************/
void image_mk_info(){
                                                                                                                                              
	int i,m,n;
	int k;
	i=0;
	n=0;
	
	for(k = 0; k < gazosize; k++){
		info_seq[n][i] = digital_pic[k];   //�����_���ȏ��n������
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
		��M��쐬
***********************************************************/
void make_received_word(){

	int n;
	double sigma;

	init_mrnd( rand() );			// rand() �̕����͗����̎�
	init_gaussd(_init[7], _func[7], rand());

	channel_var = 1.0 / (2.0 * R * pow(10.0,snr/10.0));	// �G���̕��U
	sigma = sqrt(channel_var);	// �G���̕W���΍�

	for(n = 0; n < N; n++){
		noise[n] = gaussd(0,sigma);		// ���ςƕW���΍��ɑΉ������G���쐬
		rword[n] = 1.0 - 2.0*codeword[n] + noise[n];	// BPSK�ϒ���ɎG���������Ď�M��쐬
	}
	/*for(n = 50; n < 250; n++){//����
		rword[n]=0;
	}*/
	

}
/***********************************************************
		�ΐ��ޓx����o��
***********************************************************/
/*
void print_LLR(){

	int n;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER�o�̓t�@�C�����J��
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
		��������o��
***********************************************************/
void print_codeword(){

	int n;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER�o�̓t�@�C�����J��
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
		�����O�̌��r�b�g���A���u���b�N���𐔂���
***********************************************************/
void undecoded_error_count(){

	int n,error=0;

	for(n = 0; n < N; n++){	// �d���蕜�����s��
		if(rword[n] >= 0.0)
			temp_bit[n] = 0;
		else
			temp_bit[n] = 1;
	}

	if(encoding == 0){	// all 0 �̎�
		for(n = 0; n < N; n++)
			error += temp_bit[n];	// ���r�b�g���𐔂���
	}
	else{	// not all 0 �̎�
		for(n = 0; n < N; n++)
			error += temp_bit[n] ^ codeword[n];	// ���r�b�g���𐔂���
	}

	if(error > 0){		// �����O�̌��r�b�g���A���u���b�N�����X�V
		undecoded_error_blocks++;
		undecoded_error_bits += error;
	}


}

/***********************************************************
		�ΐ��ޓx��v�Z
***********************************************************/
void get_LLR(){

	int n;

	for(n = 0; n < N; n++){
		LLR[n] = 2.0 * rword[n] / channel_var;
	}
}

/***********************************************************
		sign�֐�
***********************************************************/
int sign(double x){

	if(x >= 0.0)
		return 1;
	else
		return -1;
}

/***********************************************************
		�Â�f�֐�
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
		temp_bit_map�̏�����
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
		temp_bit_map�����n��ɖ߂�
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
		Shuffled BP Sum-Product�����@�̏�����
***********************************************************/
void init_Shuffled_BP_Sum_Product(){

	int m,n,i;

	get_LLR();		// �ΐ��ޓx��v�Z
	for(m = 0; m < M; m++){
		for(i = 0; i < row_weight[m]; i++){
			z[m][i] = LLR[A[m][i]];	// �ΐ����O�l����̏�����	(m�s��i�Ԗڂ̗v�f��\��)
		}
	}
	for(n = 0; n < N; n++){
		order[n] = n;	// �������鏇����ݒ�(bit_serial������0�`N-1)
	}
}
/***********************************************************
		�O���l�Ǝ��O�l���o��
***********************************************************/
/*
void print_alpha_beta(){

	int i,j,n,m;
	int morder[N];
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER�o�̓t�@�C�����J��
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
		�������o��
***********************************************************/
/*
void print_tempbit(){

	int i;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER�o�̓t�@�C�����J��
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
		tanh Shuffled BP Sum-Product�����@
***********************************************************/
void tanh_Shuffled_BP_Sum_Product(){

	int i,j,n,iteration,count,ite;
	double sum,prod;

	// Step 1: �������i�����l����A�ΐ��ޓx��v�Z�j
	init_Shuffled_BP_Sum_Product();
	ite=1;
	//�J��Ԃ�������������
	for(iteration = 0; iteration < max_iteration; iteration++){
		// Step 2: �s����
		for(n = 0; n < N; n++){
			sum = LLR[order[n]];
			for(i = 0; i < col_weight[order[n]]; i++){		// order[n]���i�Ԗڂ�r�����߂�
				prod = 1.0;// �������߂�ۂɕK�v�Ȑς̏�����
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i] ][j] != order[n]){	// B[order[n]][i]�s��j�Ԗڂ̗�C���f�b�N�X��order[n]�łȂ��Ƃ�
//						temp = LLR[A[B[order[n]][i]][j]] + beta[ B[order[n]][i] ][j];
//						sum += Gallager_f( fabs(temp) );	// temp�̐�Βl�𑫂����킹�Ă���
//						prod *= sign(temp);					// temp�̕������|�������
						prod *= tanh(z[B[order[n]][i]][j] / 2.0);
					}
				}
				r[order[n]][i] = prod;// * Gallager_f(sum);	// order[n]���i�Ԗڂ�r
				ip[order[n]][i] = ipusiron(prod);// order[n]���i�Ԗڂ̃�
				sum += ip[order[n]][i];
			}
			// Step 3: �񏈗�
//			sum = 0.0;			// �������߂�ۂɕK�v�Șa�̏�����
//			for(i = 0; i < col_weight[order[n]]; i++){
//				sum += ip[order[n]][i];		// order[n]��ڂ̑ΐ��O���l��𑫂����킹�Ă���
//			}
//			sum += LLR[order[n]];
			total_ipusiron[order[n]] = sum;		// n��ڂ̑��O���������߂�
			for(i = 0; i < col_weight[order[n]]; i++){
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i]][j] == order[n]){	// B[order[n]][i]�s��j�Ԗڂ̗�C���f�b�N�X��n�̂Ƃ�
						z[B[order[n]][i]][j] = total_ipusiron[order[n]] - ip[order[n]][i];	// B[order[n]][i]�s��j�Ԗڂ̑ΐ����O�l������X�V
					}							// (���O����񂩂玩���̑ΐ��O���l�������)
				}
			}
		}
		// Step 4: �I������
		for(n = 0; n < N; n++){		// �ꎞ���������߂�
			if(sign(total_ipusiron[n]) == 1)
				temp_bit[n] = 0;
			else
				temp_bit[n] = 1;
		}
		count = 0;		// �I�������𖞂������ǂ������ׂ邽�߂̕ϐ�
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
			for(n = 0; n < N; n++){		// �ꎞ�����̕ۑ�
				temp_bit_map[ite][CN][n]=temp_bit[n];
			}
		}
		if(count == 0){
			ite_count += iteration+1;
			syndrome_check = iteration+1;
			break;	// �����ɐ���
		}

	}
	if(count != 0){
		ite_count += max_iteration;
	}
		//�J��Ԃ����������܂�
}
/***********************************************************
		tanh Sum-Product�����@
***********************************************************/
void tanh_Sum_Product(){

	int i,j,n,iteration,count,ite;
	double sum,prod;

	// Step 1: �������i�����l����A�ΐ��ޓx��v�Z�j
	init_Shuffled_BP_Sum_Product();
	ite=1;
	//�J��Ԃ�������������
	for(iteration = 0; iteration < max_iteration; iteration++){
		// Step 2: �s����
		for(n = 0; n < N; n++){
			for(i = 0; i < col_weight[order[n]]; i++){		// order[n]���i�Ԗڂ�r�����߂�
				prod = 1.0;// �������߂�ۂɕK�v�Ȑς̏�����
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i] ][j] != order[n]){	// B[order[n]][i]�s��j�Ԗڂ̗�C���f�b�N�X��order[n]�łȂ��Ƃ�
//						temp = LLR[A[B[order[n]][i]][j]] + beta[ B[order[n]][i] ][j];
//						sum += Gallager_f( fabs(temp) );	// temp�̐�Βl�𑫂����킹�Ă���
//						prod *= sign(temp);					// temp�̕������|�������
						prod *= tanh(z[B[order[n]][i]][j] / 2.0);
					}
				}
				r[order[n]][i] = prod;// * Gallager_f(sum);	// order[n]���i�Ԗڂ�r
				ip[order[n]][i] = ipusiron(prod);// order[n]���i�Ԗڂ̃�
			}
		}
		for(n = 0; n < N; n++){
			// Step 3: �񏈗�
			sum = 0.0;			// �������߂�ۂɕK�v�Șa�̏�����
			for(i = 0; i < col_weight[order[n]]; i++){
				sum += ip[order[n]][i];		// order[n]��ڂ̑ΐ��O���l��𑫂����킹�Ă���
			}
			sum += LLR[order[n]];
			total_ipusiron[order[n]] = sum;		// n��ڂ̑��O���������߂�
			for(i = 0; i < col_weight[order[n]]; i++){
				for(j = 0; j < row_weight[ B[order[n]][i] ]; j++){
					if(A[ B[order[n]][i]][j] == order[n]){	// B[order[n]][i]�s��j�Ԗڂ̗�C���f�b�N�X��n�̂Ƃ�
						z[B[order[n]][i]][j] = total_ipusiron[order[n]] - ip[order[n]][i];	// B[order[n]][i]�s��j�Ԗڂ̑ΐ����O�l������X�V
					}							// (���O����񂩂玩���̑ΐ��O���l�������)
				}
			}
		}
		// Step 4: �I������
		for(n = 0; n < N; n++){		// �ꎞ���������߂�
			if(sign(total_ipusiron[n]) == 1)
				temp_bit[n] = 0;
			else
				temp_bit[n] = 1;
		}
		count = 0;		// �I�������𖞂������ǂ������ׂ邽�߂̕ϐ�
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
			for(n = 0; n < N; n++){		// �ꎞ�����̕ۑ�
				temp_bit_map[ite][CN][n]=temp_bit[n];
			}
		}
		if(count == 0){
			ite_count += iteration+1;
			syndrome_check = iteration+1;
			break;	// �����ɐ���
		}

	}
	if(count != 0){
		ite_count += max_iteration;
	}
		//�J��Ԃ����������܂�
}
/***********************************************************
		������̌��r�b�g���A���u���b�N���𐔂���
***********************************************************/
void error_count(){

	int n,error=0;

	if(encoding == 0){	// all 0 �̎�
		for(n = 0; n < N; n++){
			count_error[n] += temp_bit[n];
			error += temp_bit[n];	// ���r�b�g���𐔂���
		}
	}
	else{	// not all 0 �̎�
		for(n = 0; n < N; n++)
			error += temp_bit[n] ^ codeword[n];	// ���r�b�g���𐔂���
	}

	if(error > 0){		// ������̌��r�b�g���A���u���b�N�����X�V
		error_blocks++;						//�������s���̌��u���b�N�����X�V
		error_bits += error;			//�������s���̌��r�b�g�����X�V
		if(syndrome_check != 0){
			syndrome_error_blocks++;		//�p���e�B�`�F�b�N���s���̃G���[�u���b�N���X�V
			syndrome_error_bits += error;	//�p���e�B�`�F�b�N���s���̃G���[�r�b�g�X�V
			syndrome_error_ite_count += syndrome_check;	//�p���e�B�`�F�b�N���s���̌J��Ԃ��񐔍X�V
		}
	}
}
/***********************************************************
		���ʂ̏o��
***********************************************************/
/*
void print_result(){

	int i;
	FILE *fp;

	if((fp = fopen(outfile,"a")) == NULL){	// BER�o�̓t�@�C�����J��
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
		���ʂ̏o�� csv�`��
***********************************************************/
void print_result_csv(){

	int i;
	FILE *fp;

	if((fp = fopen(outfile2,"a")) == NULL){	// BER�o�̓t�@�C�����J��
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
		���M�����ꐔ���Œ肵�ẴV�~�����[�V����
***********************************************************/
/*void simulation_loop1(){

	int n,code,parcent=0;

	process_counter_start();		//�v���Z�X�J�E���^start
	printf("�i�s��\n");
	for(snr = min_snr; snr <= max_snr; snr += snr_interval){
		undecoded_error_blocks = 0;	// �����O�̌��u���b�N��������
		undecoded_error_bits = 0;	// �����O�̌��r�b�g��������
		error_blocks = 0;	// ������̌��u���b�N��������
		error_bits = 0;		// ������̌��r�b�g��������
		ite_count = 0;
		for(n = 0; n < N; n++){
			count_error[n] = 0;
		}
		for(code = 0; code < code_number; code++){
			parcent++;
			printf("%4.2f��\r",(parcent) / (code_number * ((max_snr-min_snr)/snr_interval+1.0)) * 100);
			if(encoding == 0){	// all 0 �̎�
				for(n = 0; n < N; n++)
					codeword[n] = 0;	// ������쐬
			}
			else{				// not all 0 �̎�
				mk_info();
				encode();
			}
			make_received_word();	// ��M��쐬
			undecoded_error_count();	// �����O�̌��r�b�g���A���u���b�N���𐔂���
			Shuffled_BP_Sum_Product();	// Bit Serial Sum-Product�����@
			error_count();		// ������̌��r�b�g���A���u���b�N���𐔂���
		}
		print_result();		// ���ʂ̏o��
	}
	process_counter_finish("finish");	// �v���Z�X�J�E���^finish
}*/
/***********************************************************
		csv�`��image�V�~�����[�V����
***********************************************************/
void simulation_loop(){

	int n;
	int i,j;
//	printf("progress\n");
	process_counter_start();		///�v���Z�X�J�E���^start
	image_mk_info();				// �摜���𕄍����ł���傫���ɕ�������
	
//	printf("progress2\n");
	for(CN = 0; CN < code_number; CN++){
		undecoded_error_blocks = 0;	// �����O�̌��u���b�N��������
		undecoded_error_bits = 0;	// �����O�̌��r�b�g��������
		error_blocks = 0;	// ������̌��u���b�N��������
		error_bits = 0;		// ������̌��r�b�g��������
		ite_count = 0;		// ������̌J��Ԃ��񐔏�����
		syndrome_error_ite_count = 0;	// �p���e�B�`�F�b�N���s���̌J��Ԃ��񐔏�����
		syndrome_error_bits = 0;		// �p���e�B�`�F�b�N���s���̌��r�b�g��������
		syndrome_error_blocks = 0;		// �p���e�B�`�F�b�N���s���̌��u���b�N��������
		for(n = 0; n < N; n++){
			count_error[n] = 0;
		}
//		parcent++;
//		printf("%4.2fpersent\r",(parcent) / (code_number * ((max_snr-min_snr)/snr_interval+1.0)) * 100);
		/*
		if(encoding == 0){	// all 0 �̎�
			for(n = 0; n < N; n++){
				codeword[n] = 0;	// ������쐬
			}
		}else{				// not all 0 �̎�
			mk_info();
			encode();
		}
		*/
//		printf("A\n");
		mk_info();
		encode();
//		printf("A\n");
		syndrome_check = 0;		// �p���e�B�`�F�b�N�Ď��֐�������
//		print_codeword();
		make_received_word();	// ��M��쐬
//		printf("A\n");
		init_temp_bit_map();	//tempbit�̏�����
//		printf("A\n");
		undecoded_error_count();	// �����O�̌��r�b�g���A���u���b�N���𐔂���
//		print_codeword();
		if(decode==0){
			tanh_Shuffled_BP_Sum_Product();	// Bit Serial Sum-Product�����@
		}else if(decode==1){
			tanh_Sum_Product();
		}
//		printf("A\n");
//		print_tempbit();
		error_count();		// ������̌��r�b�g���A���u���b�N���𐔂���
//		print_result_csv();		// ���ʂ̏o��
	}
	unit_temp_bit();				// �������������𓝍�����
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

	process_counter_finish("finish");	// �v���Z�X�J�E���^finish
}


/***********************************************************
		���M�����ꐔ���ς��ẴV�~�����[�V����
***********************************************************/
/*void simulation_loop2(){

	int n;

	for(snr = min_snr; snr <= max_snr; snr += snr_interval){
		total_blocks = 0;	// ���M�����ꐔ������
		total_bits = 0;		// ���M�r�b�g��������
		undecoded_error_blocks = 0;	// �����O�̌��u���b�N��������
		undecoded_error_bits = 0;	// �����O�̌��r�b�g��������
		error_blocks = 0;	// ������̌��u���b�N��������
		error_bits = 0;		// ������̌��r�b�g��������
		while(1){	// �I�������𖞂����܂Ń��[�v
			total_blocks++;		// ���M�����ꐔ�X�V
			total_bits += N;	// ���M�r�b�g���X�V

			if(encoding == 0){	// all 0 �̎�
				for(n = 0; n < N; n++)
					codeword[n] = 0;	// ������쐬
			}
			else{				// not all 0 �̎�
				mk_info();
				encode();
			}
			make_received_word();	// ��M��쐬
			undecoded_error_count();	// �����O�̌��r�b�g���A���u���b�N���𐔂���
			Shuffled_BP_Sum_Product();	// Bit Serial Sum-Product�����@
			error_count();		// ������̌��r�b�g���A���u���b�N���𐔂���
			if((error_bits >= target_bits) && (stop_condition == 0))	// �w�肵�����r�b�g���ɒB������break
				break;
			if((error_blocks >= target_blocks) && (stop_condition == 1))	// �w�肵�����u���b�N���ɒB������break
				break;
			if(total_blocks == code_number)	// �ő呗�M�����ꐔ�ɒB������break
				break;
		}
		print_result();		// ���ʂ̏o��
	}
}
*/
/***********************************************************
		SN��A���M�����ꐔ���w�肵�ẴV�~�����[�V����
***********************************************************/
/*void simulation_loop3(){
}*/

/***********************************************************
		�J��Ԃ����Ɍ�藦���v�Z����V�~�����[�V����
***********************************************************/
/*void simulation_loop4(){

	int i,n,code,parcent=0;

	process_counter_start();		// �v���Z�X�J�E���^start 
	printf("�i�s��\n");
	for(snr = min_snr; snr <= max_snr; snr += snr_interval){
		for(i = 0; i < max_iteration; i++)
			iteration_error[i] = 0;	// �J��Ԃ��񐔖��̌��r�b�g��������
		for(code = 0; code < code_number; code++){
			parcent++;
			printf("%4.2f��\r",(double)parcent / (double)code_number * 100);
			if(encoding == 0){	// all 0 �̎�
				for(n = 0; n < N; n++)
					codeword[n] = 0;	// ������쐬
			}
			else{				// not all 0 �̎�
				mk_info();
				encode();
			}
			make_received_word();	// ��M��쐬
			Shuffled_BP_Sum_Product();		// Sum-Product�����@
		}
		print_result();		// ���ʂ̏o��
	}
	process_counter_finish("finish");	// �v���Z�X�J�E���^finish
}*/


/***********************************************************
		�m�ۂ����̈�̊J��
***********************************************************/
void free_memory(){

	free(col_weight);	// �e��̗�d��
	free(row_weight);	// �e�s�̍s�d��
	free(A);			// �g�̂��s�ڂ̗�C���f�b�N�X�W���`
	free(B);			// �g�̂���ڂ̍s�C���f�b�N�X�W���a
	free(Gcol_weight);       // �e��̗�d��
    free(Grow_weight);       // �e�s�̍s�d��
    free(GA);           // G�̂��s�ڂ̗�C���f�b�N�X�W���`
    free(GB);           // G�̂���ڂ̍s�C���f�b�N�X�W���a
	free(codeword);		// ������
	free(noise);		// �G���n��
	free(rword);		// ��M��
	free(LLR);			// �ΐ��ޓx��
	free(r);			// ��
	free(ip);			// ��
	free(z);			// z
	free(total_ipusiron);	// ���O�����
	free(temp_bit);		// �ꎞ�����
	/*
	free(iteration_error);	// �J��Ԃ��񐔖��̌��r�b�g��
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
		main�֐�
***********************************************************/
int main(){

	srand((unsigned int)time(NULL));		// �����̎�
	
	count = 0;
	

	read_MacKay_format();	// �����s��t�@�C���̓ǂݍ���
	load_image();			// �摜�t�@�C���̓ǂݍ���
	print_parameter_csv();	// csv�V�~�����[�V�����p�����[�^�̏o��
	get_memory();			// �K�v�ȗ̈�̊m��
	simulation_loop();
	free_memory();			// �m�ۂ����̈�̊J��

	return 0;
}
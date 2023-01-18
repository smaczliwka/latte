@dnl = internal constant [4 x i8] c"%d\0A\00"
@fnl = internal constant [6 x i8] c"%.1f\0A\00"
@d   = internal constant [3 x i8] c"%d\00"	
@lf  = internal constant [4 x i8] c"%lf\00"	
@err = internal constant [14 x i8] c"RUNTIME ERROR\00"

declare i32 @printf(i8*, ...) 
declare i32 @scanf(i8*, ...)
declare i32 @puts(i8*)
declare void @exit(i32)
declare i32 @strlen(i8*)
declare i8* @strcpy(i8*, i8*)
declare i8* @strcat(i8*, i8*)
declare i32 @strcmp(i8*, i8*)
declare i32 @getchar()

declare i64 @getline(i8** noundef, i64* noundef, %struct._IO_FILE* noundef)
declare i8* @malloc(i32)
%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque
@stdin = external global %struct._IO_FILE*, align 8

define void @printInt(i32 %x) {
       %t0 = getelementptr [4 x i8], [4 x i8]* @dnl, i32 0, i32 0
       call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
       ret void
}

define void @printString(i8* %s) {
entry:  call i32 @puts(i8* %s)
	ret void
}

define void @error() {
    %t1 = bitcast [14 x i8]* @err to i8*
    call void @printString(i8* %t1)
    call void @exit(i32 1)
    ret void
}

define i32 @readInt() {
entry:	%res = alloca i32
        %t1 = getelementptr [3 x i8], [3 x i8]* @d, i32 0, i32 0
	call i32 (i8*, ...) @scanf(i8* %t1, i32* %res)
	%t2 = load i32, i32* %res
	%t3 = call i32 @getchar()
	ret i32 %t2
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @readString() #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  %3 = alloca i64, align 8
  %4 = alloca i32, align 4
  store i8* null, i8** %2, align 8
  %5 = load %struct._IO_FILE*, %struct._IO_FILE** @stdin, align 8
  %6 = call i64 @getline(i8** noundef %2, i64* noundef %3, %struct._IO_FILE* noundef %5)
  %7 = trunc i64 %6 to i32
  store i32 %7, i32* %4, align 4
  %8 = load i32, i32* %4, align 4
  %9 = icmp slt i32 %8, 0
  br i1 %9, label %10, label %11

10:                                               ; preds = %0
  store i8* null, i8** %1, align 8
  br label %18

11:                                               ; preds = %0
  %12 = load i8*, i8** %2, align 8
  %13 = load i32, i32* %4, align 4
  %14 = sub nsw i32 %13, 1
  %15 = sext i32 %14 to i64
  %16 = getelementptr inbounds i8, i8* %12, i64 %15
  store i8 0, i8* %16, align 1
  %17 = load i8*, i8** %2, align 8
  store i8* %17, i8** %1, align 8
  br label %18

18:                                               ; preds = %11, %10
  %19 = load i8*, i8** %1, align 8
  ret i8* %19
}

define i8* @_strCat(i8* %s1, i8* %s2) {
	%t1 = call i32 @strlen(i8* %s1)
	%t2 = call i32 @strlen(i8* %s2)
	%t3 = add i32 %t1, 1
	%t4 = add i32 %t3, %t2
	%t5 = call i8* @malloc(i32 %t4)
	%t6 = call i8* @strcpy(i8* %t5, i8* %s1)
	%t7 = call i8* @strcat(i8* %t6, i8* %s2)
	ret i8* %t7
}

define i1 @_strLTH(i8* %s1, i8* %s2) {
  %r = call i32 @strcmp(i8* %s1, i8* %s2)
  %b = icmp slt i32 %r, 0
  ret i1 %b
}

define i1 @_strLE(i8* %s1, i8* %s2) {
  %r = call i32 @strcmp(i8* %s1, i8* %s2)
  %b = icmp sle i32 %r, 0
  ret i1 %b
}

define i1 @_strGTH(i8* %s1, i8* %s2) {
  %r = call i32 @strcmp(i8* %s1, i8* %s2)
  %b = icmp sgt i32 %r, 0
  ret i1 %b
}

define i1 @_strGE(i8* %s1, i8* %s2) {
  %r = call i32 @strcmp(i8* %s1, i8* %s2)
  %b = icmp sge i32 %r, 0
  ret i1 %b
}

define i1 @_strEQU(i8* %s1, i8* %s2) {
  %r = call i32 @strcmp(i8* %s1, i8* %s2)
  %b = icmp eq i32 %r, 0
  ret i1 %b
}

define i1 @_strNE(i8* %s1, i8* %s2) {
  %r = call i32 @strcmp(i8* %s1, i8* %s2)
  %b = icmp ne i32 %r, 0
  ret i1 %b
}

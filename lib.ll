@dnl    = internal constant [4 x i8] c"%d\0A\00"
@fnl    = internal constant [6 x i8] c"%.1f\0A\00"
@d      = internal constant [3 x i8] c"%d\00"	
@lf     = internal constant [4 x i8] c"%lf\00"	
@s      = internal constant [3 x i8] c"%s\00"	
@err    = internal constant [6 x i8] c"error\00"

declare i32 @printf(i8*, ...) 
declare i32 @scanf(i8*, ...)
declare i32 @puts(i8*)
declare i8* @malloc(i32)
declare i32 @strlen(i8*)
declare i8* @strcpy(i8*, i8*)
declare i8* @strcat(i8*, i8*)

define void @printInt(i32 %x) {
    %t0 = getelementptr [4 x i8], [4 x i8]* @dnl, i32 0, i32 0
    call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
    ret void
}

define void @printDouble(double %x) {
entry:
    %t0 = getelementptr [6 x i8], [6 x i8]* @fnl, i32 0, i32 0
    call i32 (i8*, ...) @printf(i8* %t0, double %x) 
    ret void
}

define void @printString(i8* %s) {
entry:
    call i32 @puts(i8* %s)
    ret void
}

define i32 @readInt() {
entry:	
    %res = alloca i32
    %t1 = getelementptr [3 x i8], [3 x i8]* @d, i32 0, i32 0
    call i32 (i8*, ...) @scanf(i8* %t1, i32* %res)
    %t2 = load i32, i32* %res
    ret i32 %t2
}

define double @readDouble() {
entry:
    %res = alloca double
    %t1 = getelementptr [4 x i8],[4 x i8]* @lf, i32 0, i32 0
    call i32 (i8*, ...) @scanf(i8* %t1, double* %res)
    %t2 = load double, double* %res
    ret double %t2
}

define void @error() {
entry:
    %t1 = getelementptr [6 x i8], [6 x i8]* @err, i32 0, i32 0
    call i32 @puts(i8* %t1)
    ret void
}

define i8* @readString() {
entry:	
    %res = call i8* @malloc(i32 124)
    %t1 = getelementptr [3 x i8], [3 x i8]* @s, i32 0, i32 0
    call i32 (i8*, ...) @scanf(i8* %t1, i8* %res)
    ret i8* %res
}

define i8* @.strconcat(i8* %s1, i8* %s2) {
entry:
    %t1 = call i32 @strlen(i8* %s1)
    %t2 = call i32 @strlen(i8* %s2)
    %t3 = add i32 %t1, 1
    %t4 = add i32 %t3, %t2
    %t5 = call i8* @malloc(i32 %t4)
    %t6 = call i8* @strcpy(i8* %t5, i8* %s1)
    %t7 = call i8* @strcat(i8* %t6, i8* %s2)
    ret i8* %t7 
}

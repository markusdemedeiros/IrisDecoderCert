.intel_syntax noprefix
.code64
.section .text.ff_aac_sbr_apply,"ax",@progbits
.globl ff_aac_sbr_apply
.type ff_aac_sbr_apply,@function
ff_aac_sbr_apply:
__sbr_cell_0_0:
    push rbp
__sbr_cell_0_0_end:
__sbr_cell_0_1:
    mov rbp, rsp
__sbr_cell_0_1_end:
__sbr_cell_0_2:
    push r15
__sbr_cell_0_2_end:
__sbr_cell_0_3:
    push r14
__sbr_cell_0_3_end:
__sbr_cell_0_4:
    push r13
__sbr_cell_0_4_end:
__sbr_cell_0_5:
    push r12
__sbr_cell_0_5_end:
__sbr_cell_0_6:
    push rbx
__sbr_cell_0_6_end:
__sbr_cell_0_7:
    sub rsp, 408
__sbr_cell_0_7_end:
__sbr_cell_0_8:
    mov QWORD PTR [rbp-296], r8
__sbr_cell_0_8_end:
__sbr_cell_0_9:
    mov QWORD PTR [rbp-304], rcx
__sbr_cell_0_9_end:
ff_aac_sbr_apply.start_1:
__sbr_cell_0_10:
    mov eax, DWORD PTR [rdi+22516]
__sbr_cell_0_10_end:
__sbr_cell_0_11:
    xor r14d, r14d
__sbr_cell_0_11_end:
__sbr_cell_0_12:
    cmp eax, DWORD PTR [rsi+166176]
__sbr_cell_0_12_end:
__sbr_cell_0_13:
    setl BYTE PTR [rbp-240]
__sbr_cell_0_13_end:
__sbr_cell_0_14:
    cmp edx, 1
__sbr_cell_0_14_end:
__sbr_cell_0_15:
    sete al
__sbr_cell_0_15_end:
ff_aac_sbr_apply.start_2:
__sbr_cell_0_16:
    mov r8d, DWORD PTR [rsi+166188]
__sbr_cell_0_16_end:
__sbr_cell_0_17:
    cmp edx, r8d
__sbr_cell_0_17_end:
__sbr_cell_0_18:
    mov QWORD PTR [rbp-56], rsi
__sbr_cell_0_18_end:
__sbr_cell_0_19:
    mov QWORD PTR [rbp-144], rdi
__sbr_cell_0_19_end:
__sbr_cell_0_20:
    mov BYTE PTR [rbp-57], al
__sbr_cell_0_20_end:
__sbr_cell_0_21:
    mov DWORD PTR [rbp-156], edx
__sbr_cell_0_21_end:
__sbr_cell_0_22:
    jne ff_aac_sbr_apply.L6797
__sbr_cell_0_22_end:
__sbr_cell_0_23:
    mov r9, rsi
__sbr_cell_0_23_end:
__sbr_cell_0_24:
    mov bl, 1
__sbr_cell_0_24_end:
__sbr_cell_0_25:
    cmp DWORD PTR [rsi+166180], 0
__sbr_cell_0_25_end:
__sbr_cell_0_26:
    je ff_aac_sbr_apply.L6817
__sbr_cell_0_26_end:
__sbr_cell_0_27:
    cmp DWORD PTR [r9+166184], 0
__sbr_cell_0_27_end:
__sbr_cell_0_28:
    je ff_aac_sbr_apply.L6f32
__sbr_cell_0_28_end:
__sbr_cell_0_29:
    xor ebx, ebx
__sbr_cell_0_29_end:
__sbr_cell_0_30:
    cmp DWORD PTR [r9+166276], 0
__sbr_cell_0_30_end:
ff_aac_sbr_apply.start_3:
__sbr_cell_0_31:
    jne ff_aac_sbr_apply.L6825
__sbr_cell_0_31_end:
ff_aac_sbr_apply.L676e:
__sbr_cell_0_32:
    mov eax, DWORD PTR [r9+166264]
__sbr_cell_0_32_end:
__sbr_cell_0_33:
    mov ecx, DWORD PTR [r9+166272]
__sbr_cell_0_33_end:
__sbr_cell_0_34:
    mov DWORD PTR [r9+166260], eax
__sbr_cell_0_34_end:
__sbr_cell_0_35:
    mov DWORD PTR [r9+166268], ecx
__sbr_cell_0_35_end:
__sbr_cell_0_36:
    test bl, bl
__sbr_cell_0_36_end:
__sbr_cell_0_37:
    jne ff_aac_sbr_apply.L74e9
__sbr_cell_0_37_end:
__sbr_cell_0_38:
    jmp ff_aac_sbr_apply.L6838
__sbr_cell_0_38_end:
ff_aac_sbr_apply.L6797:
__sbr_cell_0_39:
    mov ecx, edx
__sbr_cell_0_39_end:
__sbr_cell_0_40:
    mov rdi, QWORD PTR [rdi+8]
__sbr_cell_0_40_end:
__sbr_cell_0_41:
    xor esi, esi
__sbr_cell_0_41_end:
__sbr_cell_0_42:
    cmp edx, 3
__sbr_cell_0_42_end:
__sbr_cell_0_43:
    sete sil
__sbr_cell_0_43_end:
__sbr_cell_0_44:
    shl esi, 4
__sbr_cell_0_44_end:
__sbr_cell_0_45:
    add esi, 24
__sbr_cell_0_45_end:
__sbr_cell_0_46:
    lea rdx, [rip+L_str_1]
__sbr_cell_0_46_end:
__sbr_cell_0_47:
    xor eax, eax
__sbr_cell_0_47_end:
__sbr_cell_0_48:
    call av_log
__sbr_cell_0_48_end:
ff_aac_sbr_apply.L6797_1:
__sbr_cell_0_49:
    mov r9, QWORD PTR [rbp-56]
__sbr_cell_0_49_end:
__sbr_cell_0_50:
    mov QWORD PTR [r9+166180], 0
__sbr_cell_0_50_end:
__sbr_cell_0_51:
    mov DWORD PTR [r9+166192], 0
__sbr_cell_0_51_end:
__sbr_cell_0_52:
    mov DWORD PTR [r9+166264], 32
__sbr_cell_0_52_end:
__sbr_cell_0_53:
    mov DWORD PTR [r9+166272], 0
__sbr_cell_0_53_end:
__sbr_cell_0_54:
    mov DWORD PTR [r9+269672], 4294967295
__sbr_cell_0_54_end:
__sbr_cell_0_55:
    mov DWORD PTR [r9+180904], 4294967295
__sbr_cell_0_55_end:
__sbr_cell_0_56:
    mov DWORD PTR [r9+166204], 4294967295
__sbr_cell_0_56_end:
__sbr_cell_0_57:
    mov WORD PTR [r9+166208], 65535
__sbr_cell_0_57_end:
__sbr_cell_0_58:
    mov bl, 1
__sbr_cell_0_58_end:
ff_aac_sbr_apply.L6817:
__sbr_cell_0_59:
    cmp DWORD PTR [r9+166276], 0
__sbr_cell_0_59_end:
__sbr_cell_0_60:
    je ff_aac_sbr_apply.L676e
__sbr_cell_0_60_end:
ff_aac_sbr_apply.L6825:
__sbr_cell_0_61:
    mov DWORD PTR [r9+166276], 0
__sbr_cell_0_61_end:
__sbr_cell_0_62:
    test bl, bl
__sbr_cell_0_62_end:
__sbr_cell_0_63:
    jne ff_aac_sbr_apply.L74e9
__sbr_cell_0_63_end:
ff_aac_sbr_apply.L6838:
__sbr_cell_0_64:
    mov eax, 1
__sbr_cell_0_64_end:
__sbr_cell_0_65:
    mov QWORD PTR [rbp-200], rax
__sbr_cell_0_65_end:
ff_aac_sbr_apply.L6838_1:
__sbr_cell_0_66:
    mov eax, DWORD PTR [rbp-156]
__sbr_cell_0_66_end:
__sbr_cell_0_67:
    cmp eax, 1
__sbr_cell_0_67_end:
__sbr_cell_0_68:
    jne ff_aac_sbr_apply.L6fca
__sbr_cell_0_68_end:
__sbr_cell_0_69:
    cmp DWORD PTR [r9+166236], 0
__sbr_cell_0_69_end:
__sbr_cell_0_70:
    je ff_aac_sbr_apply.L6fbe
__sbr_cell_0_70_end:
__sbr_cell_0_71:
    cmp DWORD PTR [r9+166404], 0
__sbr_cell_0_71_end:
__sbr_cell_0_72:
    mov eax, 24
__sbr_cell_0_72_end:
__sbr_cell_0_73:
    mov r15d, 12
__sbr_cell_0_73_end:
__sbr_cell_0_74:
    cmove r15d, eax
__sbr_cell_0_74_end:
__sbr_cell_0_75:
    cmp DWORD PTR [r9+166312], 0
__sbr_cell_0_75_end:
__sbr_cell_0_76:
    je ff_aac_sbr_apply.L6abf
__sbr_cell_0_76_end:
__sbr_cell_0_77:
    lea r12, [r9+341616]
__sbr_cell_0_77_end:
__sbr_cell_0_78:
    lea r13, [r9+342192]
__sbr_cell_0_78_end:
__sbr_cell_0_79:
    mov ebx, 1
__sbr_cell_0_79_end:
__sbr_cell_0_80:
    vmovsd xmm2, QWORD PTR [rip+LCPI14_4]
__sbr_cell_0_80_end:
ff_aac_sbr_apply.L6838_2:
__sbr_cell_0_81:
    vmovss xmm3, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_81_end:
__sbr_cell_0_82:
    .nops 1
__sbr_cell_0_82_end:
ff_aac_sbr_apply.L68b0:
__sbr_cell_0_83:
    movzx eax, BYTE PTR [r9+rbx*1+166316]
__sbr_cell_0_83_end:
__sbr_cell_0_84:
    cmp al, 1
__sbr_cell_0_84_end:
__sbr_cell_0_85:
    ja ff_aac_sbr_apply.L6ff7
__sbr_cell_0_85_end:
__sbr_cell_0_86:
    xor r14d, r14d
__sbr_cell_0_86_end:
__sbr_cell_0_87:
    jmp ff_aac_sbr_apply.L68f8
__sbr_cell_0_87_end:
__sbr_cell_0_88:
    .nops 1
__sbr_cell_0_88_end:
ff_aac_sbr_apply.L68d0:
__sbr_cell_0_89:
    vaddss xmm1, xmm4, xmm3
__sbr_cell_0_89_end:
__sbr_cell_0_90:
    vdivss xmm0, xmm0, xmm1
__sbr_cell_0_90_end:
__sbr_cell_0_91:
    vmovss DWORD PTR [r13+r14*4-88768], xmm0
__sbr_cell_0_91_end:
__sbr_cell_0_92:
    vmulss xmm0, xmm4, xmm0
__sbr_cell_0_92_end:
ff_aac_sbr_apply.L68d0_1:
__sbr_cell_0_93:
    vmovss DWORD PTR [r13+r14*4+0], xmm0
__sbr_cell_0_93_end:
__sbr_cell_0_94:
    inc r14
__sbr_cell_0_94_end:
__sbr_cell_0_95:
    cmp al, 2
__sbr_cell_0_95_end:
__sbr_cell_0_96:
    jae ff_aac_sbr_apply.L6ff7
__sbr_cell_0_96_end:
ff_aac_sbr_apply.L68f8:
__sbr_cell_0_97:
    movzx ecx, al
__sbr_cell_0_97_end:
__sbr_cell_0_98:
    mov ecx, DWORD PTR [r9+rcx*4+477952]
__sbr_cell_0_98_end:
__sbr_cell_0_99:
    cmp r14, rcx
__sbr_cell_0_99_end:
__sbr_cell_0_100:
    jae ff_aac_sbr_apply.L6a90
__sbr_cell_0_100_end:
__sbr_cell_0_101:
    cmp DWORD PTR [r9+166404], 0
__sbr_cell_0_101_end:
__sbr_cell_0_102:
    je ff_aac_sbr_apply.L6940
__sbr_cell_0_102_end:
__sbr_cell_0_103:
    cmp r14, 48
__sbr_cell_0_103_end:
__sbr_cell_0_104:
    jae ff_aac_sbr_apply.L9b63
__sbr_cell_0_104_end:
__sbr_cell_0_105:
    movzx ecx, BYTE PTR [r12+r14*1-88768]
__sbr_cell_0_105_end:
__sbr_cell_0_106:
    cmp ecx, 122
__sbr_cell_0_106_end:
__sbr_cell_0_107:
    jb ff_aac_sbr_apply.L69d0
__sbr_cell_0_107_end:
__sbr_cell_0_108:
    vmovd xmm0, DWORD PTR [rip+LCPI14_0]
__sbr_cell_0_108_end:
__sbr_cell_0_109:
    jmp ff_aac_sbr_apply.L69dd
__sbr_cell_0_109_end:
__sbr_cell_0_110:
    .nops 1
__sbr_cell_0_110_end:
ff_aac_sbr_apply.L6940:
__sbr_cell_0_111:
    cmp r14, 48
__sbr_cell_0_111_end:
__sbr_cell_0_112:
    jae ff_aac_sbr_apply.L9b6d
__sbr_cell_0_112_end:
__sbr_cell_0_113:
    movzx ecx, BYTE PTR [r12+r14*1-88768]
__sbr_cell_0_113_end:
__sbr_cell_0_114:
    movzx esi, cl
__sbr_cell_0_114_end:
__sbr_cell_0_115:
    shr esi, 1
__sbr_cell_0_115_end:
__sbr_cell_0_116:
    add esi, 7
__sbr_cell_0_116_end:
__sbr_cell_0_117:
    movzx edx, BYTE PTR [r12+r14*1+0]
__sbr_cell_0_117_end:
__sbr_cell_0_118:
    mov edi, r15d
__sbr_cell_0_118_end:
__sbr_cell_0_119:
    sub edi, edx
__sbr_cell_0_119_end:
__sbr_cell_0_120:
    vmovd xmm0, esi
__sbr_cell_0_120_end:
__sbr_cell_0_121:
    vpinsrd xmm1, xmm0, edi, 1
__sbr_cell_0_121_end:
__sbr_cell_0_122:
    vpslld xmm1, xmm1, 22
__sbr_cell_0_122_end:
__sbr_cell_0_123:
    vpslld xmm0, xmm0, 23
__sbr_cell_0_123_end:
__sbr_cell_0_124:
    vpblendw xmm0, xmm0, xmm1, 12
__sbr_cell_0_124_end:
__sbr_cell_0_125:
    vpand xmm0, xmm0, XMMWORD PTR [rip+LCPI14_1]
__sbr_cell_0_125_end:
ff_aac_sbr_apply.L6940_1:
__sbr_cell_0_126:
    vpaddd xmm0, xmm0, XMMWORD PTR [rip+LCPI14_2]
__sbr_cell_0_126_end:
__sbr_cell_0_127:
    vcvtps2pd xmm1, xmm0
__sbr_cell_0_127_end:
__sbr_cell_0_128:
    vmovapd xmm0, xmm1
__sbr_cell_0_128_end:
__sbr_cell_0_129:
    cmp cl, 244
__sbr_cell_0_129_end:
__sbr_cell_0_130:
    jb ff_aac_sbr_apply.L69a4
__sbr_cell_0_130_end:
__sbr_cell_0_131:
    vmovsd xmm0, QWORD PTR [rip+LCPI14_3]
__sbr_cell_0_131_end:
ff_aac_sbr_apply.L69a4:
__sbr_cell_0_132:
    and ecx, 1
__sbr_cell_0_132_end:
__sbr_cell_0_133:
    lea rsi, [rip+exp2_tab]
__sbr_cell_0_133_end:
__sbr_cell_0_134:
    vmulsd xmm0, xmm0, QWORD PTR [rsi+rcx*8+0]
__sbr_cell_0_134_end:
__sbr_cell_0_135:
    vcvtsd2ss xmm0, xmm0, xmm0
__sbr_cell_0_135_end:
__sbr_cell_0_136:
    and edx, 1
__sbr_cell_0_136_end:
__sbr_cell_0_137:
    vshufpd xmm1, xmm1, xmm1, 1
__sbr_cell_0_137_end:
__sbr_cell_0_138:
    vmulsd xmm1, xmm1, QWORD PTR [rsi+rdx*8+0]
__sbr_cell_0_138_end:
__sbr_cell_0_139:
    vcvtsd2ss xmm4, xmm1, xmm1
__sbr_cell_0_139_end:
__sbr_cell_0_140:
    jmp ff_aac_sbr_apply.L6a30
__sbr_cell_0_140_end:
__sbr_cell_0_141:
    .nops 1
__sbr_cell_0_141_end:
ff_aac_sbr_apply.L69d0:
__sbr_cell_0_142:
    shl ecx, 23
__sbr_cell_0_142_end:
__sbr_cell_0_143:
    add ecx, 1124073472
__sbr_cell_0_143_end:
__sbr_cell_0_144:
    vmovd xmm0, ecx
__sbr_cell_0_144_end:
ff_aac_sbr_apply.L69dd:
__sbr_cell_0_145:
    movzx edx, BYTE PTR [r12+r14*1+0]
__sbr_cell_0_145_end:
__sbr_cell_0_146:
    mov ecx, r15d
__sbr_cell_0_146_end:
__sbr_cell_0_147:
    sub ecx, edx
__sbr_cell_0_147_end:
__sbr_cell_0_148:
    lea edx, [rcx+126]
__sbr_cell_0_148_end:
__sbr_cell_0_149:
    cmp edx, 254
__sbr_cell_0_149_end:
__sbr_cell_0_150:
    ja ff_aac_sbr_apply.L6a10
__sbr_cell_0_150_end:
__sbr_cell_0_151:
    shl ecx, 23
__sbr_cell_0_151_end:
__sbr_cell_0_152:
    add ecx, 1065353216
__sbr_cell_0_152_end:
__sbr_cell_0_153:
    vmovd xmm4, ecx
__sbr_cell_0_153_end:
__sbr_cell_0_154:
    jmp ff_aac_sbr_apply.L6a30
__sbr_cell_0_154_end:
__sbr_cell_0_155:
    .nops 1
__sbr_cell_0_155_end:
ff_aac_sbr_apply.L6a10:
__sbr_cell_0_156:
    vpxor xmm4, xmm4, xmm4
__sbr_cell_0_156_end:
__sbr_cell_0_157:
    cmp ecx, 4294967147
__sbr_cell_0_157_end:
__sbr_cell_0_158:
    jb ff_aac_sbr_apply.L6a30
__sbr_cell_0_158_end:
__sbr_cell_0_159:
    add cl, 149
__sbr_cell_0_159_end:
__sbr_cell_0_160:
    mov edx, 1
__sbr_cell_0_160_end:
__sbr_cell_0_161:
    shl edx, cl
__sbr_cell_0_161_end:
__sbr_cell_0_162:
    vmovd xmm4, edx
__sbr_cell_0_162_end:
__sbr_cell_0_163:
    .nops 1
__sbr_cell_0_163_end:
ff_aac_sbr_apply.L6a30:
__sbr_cell_0_164:
    vcvtss2sd xmm1, xmm0, xmm0
__sbr_cell_0_164_end:
__sbr_cell_0_165:
    vucomisd xmm1, xmm2
__sbr_cell_0_165_end:
__sbr_cell_0_166:
    jbe ff_aac_sbr_apply.L68d0
__sbr_cell_0_166_end:
__sbr_cell_0_167:
    xor edi, edi
__sbr_cell_0_167_end:
__sbr_cell_0_168:
    mov esi, 16
__sbr_cell_0_168_end:
__sbr_cell_0_169:
    lea rdx, [rip+L_str_33]
__sbr_cell_0_169_end:
__sbr_cell_0_170:
    xor eax, eax
__sbr_cell_0_170_end:
__sbr_cell_0_171:
    vmovd DWORD PTR [rbp-48], xmm4
__sbr_cell_0_171_end:
ff_aac_sbr_apply.L6a30_1:
__sbr_cell_0_172:
    call av_log
__sbr_cell_0_172_end:
ff_aac_sbr_apply.L6a30_2:
__sbr_cell_0_173:
    vmovd xmm4, DWORD PTR [rbp-48]
__sbr_cell_0_173_end:
__sbr_cell_0_174:
    vmovss xmm3, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_174_end:
__sbr_cell_0_175:
    vmovsd xmm2, QWORD PTR [rip+LCPI14_4]
__sbr_cell_0_175_end:
__sbr_cell_0_176:
    mov r9, QWORD PTR [rbp-56]
__sbr_cell_0_176_end:
__sbr_cell_0_177:
    movzx eax, BYTE PTR [r9+rbx*1+166316]
__sbr_cell_0_177_end:
__sbr_cell_0_178:
    vmovaps xmm0, xmm3
__sbr_cell_0_178_end:
__sbr_cell_0_179:
    jmp ff_aac_sbr_apply.L68d0
__sbr_cell_0_179_end:
__sbr_cell_0_180:
    .nops 1
__sbr_cell_0_180_end:
ff_aac_sbr_apply.L6a90:
__sbr_cell_0_181:
    mov eax, DWORD PTR [r9+166312]
__sbr_cell_0_181_end:
__sbr_cell_0_182:
    cmp rbx, rax
__sbr_cell_0_182_end:
__sbr_cell_0_183:
    mov r14d, 0
__sbr_cell_0_183_end:
__sbr_cell_0_184:
    jae ff_aac_sbr_apply.L6abf
__sbr_cell_0_184_end:
__sbr_cell_0_185:
    inc rbx
__sbr_cell_0_185_end:
__sbr_cell_0_186:
    add r12, 48
__sbr_cell_0_186_end:
__sbr_cell_0_187:
    add r13, 192
__sbr_cell_0_187_end:
__sbr_cell_0_188:
    cmp rbx, 9
__sbr_cell_0_188_end:
__sbr_cell_0_189:
    jne ff_aac_sbr_apply.L68b0
__sbr_cell_0_189_end:
__sbr_cell_0_190:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_190_end:
ff_aac_sbr_apply.L6abf:
__sbr_cell_0_191:
    mov eax, DWORD PTR [r9+166328]
__sbr_cell_0_191_end:
__sbr_cell_0_192:
    test eax, eax
__sbr_cell_0_192_end:
__sbr_cell_0_193:
    je ff_aac_sbr_apply.L74de
__sbr_cell_0_193_end:
__sbr_cell_0_194:
    mov r8d, DWORD PTR [r9+477960]
__sbr_cell_0_194_end:
__sbr_cell_0_195:
    test r8d, r8d
__sbr_cell_0_195_end:
__sbr_cell_0_196:
    je ff_aac_sbr_apply.L74de
__sbr_cell_0_196_end:
__sbr_cell_0_197:
    inc eax
__sbr_cell_0_197_end:
__sbr_cell_0_198:
    mov edx, 1
__sbr_cell_0_198_end:
__sbr_cell_0_199:
    mov ecx, 1
__sbr_cell_0_199_end:
__sbr_cell_0_200:
    xor esi, esi
__sbr_cell_0_200_end:
__sbr_cell_0_201:
    vmovsd xmm0, QWORD PTR [rip+LCPI14_4]
__sbr_cell_0_201_end:
__sbr_cell_0_202:
    vmovss xmm1, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_202_end:
__sbr_cell_0_203:
    jmp ff_aac_sbr_apply.L6b12
__sbr_cell_0_203_end:
__sbr_cell_0_204:
    .nops 1
__sbr_cell_0_204_end:
ff_aac_sbr_apply.L6b00:
__sbr_cell_0_205:
    xor ecx, ecx
__sbr_cell_0_205_end:
ff_aac_sbr_apply.L6b02:
__sbr_cell_0_206:
    inc rdx
__sbr_cell_0_206_end:
__sbr_cell_0_207:
    add rsi, 5
__sbr_cell_0_207_end:
__sbr_cell_0_208:
    cmp rax, rdx
__sbr_cell_0_208_end:
__sbr_cell_0_209:
    je ff_aac_sbr_apply.L74de
__sbr_cell_0_209_end:
ff_aac_sbr_apply.L6b12:
__sbr_cell_0_210:
    test ecx, ecx
__sbr_cell_0_210_end:
__sbr_cell_0_211:
    je ff_aac_sbr_apply.L6b00
__sbr_cell_0_211_end:
__sbr_cell_0_212:
    cmp rdx, 2
__sbr_cell_0_212_end:
__sbr_cell_0_213:
    ja ff_aac_sbr_apply.L9c04
__sbr_cell_0_213_end:
__sbr_cell_0_214:
    movzx edi, BYTE PTR [r9+rsi*1+254965]
__sbr_cell_0_214_end:
__sbr_cell_0_215:
    mov ecx, 7
__sbr_cell_0_215_end:
__sbr_cell_0_216:
    sub ecx, edi
__sbr_cell_0_216_end:
__sbr_cell_0_217:
    cmp edi, 134
__sbr_cell_0_217_end:
__sbr_cell_0_218:
    jae ff_aac_sbr_apply.L6b50
__sbr_cell_0_218_end:
__sbr_cell_0_219:
    shl ecx, 23
__sbr_cell_0_219_end:
__sbr_cell_0_220:
    add ecx, 1065353216
__sbr_cell_0_220_end:
__sbr_cell_0_221:
    vmovd xmm2, ecx
__sbr_cell_0_221_end:
__sbr_cell_0_222:
    jmp ff_aac_sbr_apply.L6b6c
__sbr_cell_0_222_end:
__sbr_cell_0_223:
    .nops 1
__sbr_cell_0_223_end:
ff_aac_sbr_apply.L6b50:
__sbr_cell_0_224:
    vxorpd xmm2, xmm2, xmm2
__sbr_cell_0_224_end:
__sbr_cell_0_225:
    cmp ecx, 4294967147
__sbr_cell_0_225_end:
__sbr_cell_0_226:
    jb ff_aac_sbr_apply.L6b6c
__sbr_cell_0_226_end:
__sbr_cell_0_227:
    mov cl, 156
__sbr_cell_0_227_end:
__sbr_cell_0_228:
    sub cl, dil
__sbr_cell_0_228_end:
__sbr_cell_0_229:
    mov edi, 1
__sbr_cell_0_229_end:
__sbr_cell_0_230:
    shl edi, cl
__sbr_cell_0_230_end:
__sbr_cell_0_231:
    vmovd xmm2, edi
__sbr_cell_0_231_end:
ff_aac_sbr_apply.L6b6c:
__sbr_cell_0_232:
    movzx edi, BYTE PTR [r9+rsi*1+343733]
__sbr_cell_0_232_end:
__sbr_cell_0_233:
    mov ecx, 12
__sbr_cell_0_233_end:
__sbr_cell_0_234:
    sub ecx, edi
__sbr_cell_0_234_end:
__sbr_cell_0_235:
    cmp edi, 138
__sbr_cell_0_235_end:
__sbr_cell_0_236:
    ja ff_aac_sbr_apply.L6ba0
__sbr_cell_0_236_end:
__sbr_cell_0_237:
    shl ecx, 23
__sbr_cell_0_237_end:
__sbr_cell_0_238:
    add ecx, 1065353216
__sbr_cell_0_238_end:
__sbr_cell_0_239:
    vmovd xmm3, ecx
__sbr_cell_0_239_end:
__sbr_cell_0_240:
    jmp ff_aac_sbr_apply.L6bbc
__sbr_cell_0_240_end:
__sbr_cell_0_241:
    .nops 1
__sbr_cell_0_241_end:
ff_aac_sbr_apply.L6ba0:
__sbr_cell_0_242:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_0_242_end:
__sbr_cell_0_243:
    cmp ecx, 4294967147
__sbr_cell_0_243_end:
__sbr_cell_0_244:
    jb ff_aac_sbr_apply.L6bbc
__sbr_cell_0_244_end:
__sbr_cell_0_245:
    mov cl, 161
__sbr_cell_0_245_end:
__sbr_cell_0_246:
    sub cl, dil
__sbr_cell_0_246_end:
__sbr_cell_0_247:
    mov edi, 1
__sbr_cell_0_247_end:
__sbr_cell_0_248:
    shl edi, cl
__sbr_cell_0_248_end:
__sbr_cell_0_249:
    vmovd xmm3, edi
__sbr_cell_0_249_end:
ff_aac_sbr_apply.L6bbc:
__sbr_cell_0_250:
    vcvtss2sd xmm4, xmm2, xmm2
__sbr_cell_0_250_end:
__sbr_cell_0_251:
    vucomisd xmm0, xmm4
__sbr_cell_0_251_end:
__sbr_cell_0_252:
    jb ff_aac_sbr_apply.L9b9a
__sbr_cell_0_252_end:
__sbr_cell_0_253:
    vaddss xmm4, xmm3, xmm1
__sbr_cell_0_253_end:
__sbr_cell_0_254:
    vdivss xmm2, xmm2, xmm4
__sbr_cell_0_254_end:
__sbr_cell_0_255:
    vmovss DWORD PTR [r9+rsi*4+254996], xmm2
__sbr_cell_0_255_end:
__sbr_cell_0_256:
    vmulss xmm2, xmm3, xmm2
__sbr_cell_0_256_end:
ff_aac_sbr_apply.L6bbc_1:
__sbr_cell_0_257:
    vmovss DWORD PTR [r9+rsi*4+343764], xmm2
__sbr_cell_0_257_end:
__sbr_cell_0_258:
    mov ecx, r8d
__sbr_cell_0_258_end:
__sbr_cell_0_259:
    cmp r8d, 2
__sbr_cell_0_259_end:
__sbr_cell_0_260:
    jb ff_aac_sbr_apply.L6b02
__sbr_cell_0_260_end:
__sbr_cell_0_261:
    movzx edi, BYTE PTR [r9+rsi*1+254966]
__sbr_cell_0_261_end:
__sbr_cell_0_262:
    mov ecx, 7
__sbr_cell_0_262_end:
__sbr_cell_0_263:
    sub ecx, edi
__sbr_cell_0_263_end:
__sbr_cell_0_264:
    cmp edi, 134
__sbr_cell_0_264_end:
__sbr_cell_0_265:
    jae ff_aac_sbr_apply.L6c1e
__sbr_cell_0_265_end:
__sbr_cell_0_266:
    shl ecx, 23
__sbr_cell_0_266_end:
__sbr_cell_0_267:
    add ecx, 1065353216
__sbr_cell_0_267_end:
__sbr_cell_0_268:
    vmovd xmm2, ecx
__sbr_cell_0_268_end:
__sbr_cell_0_269:
    jmp ff_aac_sbr_apply.L6c3a
__sbr_cell_0_269_end:
ff_aac_sbr_apply.L6c1e:
__sbr_cell_0_270:
    vxorps xmm2, xmm2, xmm2
__sbr_cell_0_270_end:
__sbr_cell_0_271:
    cmp ecx, 4294967147
__sbr_cell_0_271_end:
__sbr_cell_0_272:
    jb ff_aac_sbr_apply.L6c3a
__sbr_cell_0_272_end:
__sbr_cell_0_273:
    mov cl, 156
__sbr_cell_0_273_end:
__sbr_cell_0_274:
    sub cl, dil
__sbr_cell_0_274_end:
__sbr_cell_0_275:
    mov edi, 1
__sbr_cell_0_275_end:
__sbr_cell_0_276:
    shl edi, cl
__sbr_cell_0_276_end:
__sbr_cell_0_277:
    vmovd xmm2, edi
__sbr_cell_0_277_end:
ff_aac_sbr_apply.L6c3a:
__sbr_cell_0_278:
    movzx edi, BYTE PTR [r9+rsi*1+343734]
__sbr_cell_0_278_end:
__sbr_cell_0_279:
    mov ecx, 12
__sbr_cell_0_279_end:
__sbr_cell_0_280:
    sub ecx, edi
__sbr_cell_0_280_end:
__sbr_cell_0_281:
    cmp edi, 139
__sbr_cell_0_281_end:
__sbr_cell_0_282:
    jae ff_aac_sbr_apply.L6c61
__sbr_cell_0_282_end:
__sbr_cell_0_283:
    shl ecx, 23
__sbr_cell_0_283_end:
__sbr_cell_0_284:
    add ecx, 1065353216
__sbr_cell_0_284_end:
__sbr_cell_0_285:
    vmovd xmm3, ecx
__sbr_cell_0_285_end:
__sbr_cell_0_286:
    jmp ff_aac_sbr_apply.L6c7d
__sbr_cell_0_286_end:
ff_aac_sbr_apply.L6c61:
__sbr_cell_0_287:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_0_287_end:
__sbr_cell_0_288:
    cmp ecx, 4294967147
__sbr_cell_0_288_end:
__sbr_cell_0_289:
    jb ff_aac_sbr_apply.L6c7d
__sbr_cell_0_289_end:
__sbr_cell_0_290:
    mov cl, 161
__sbr_cell_0_290_end:
__sbr_cell_0_291:
    sub cl, dil
__sbr_cell_0_291_end:
__sbr_cell_0_292:
    mov edi, 1
__sbr_cell_0_292_end:
__sbr_cell_0_293:
    shl edi, cl
__sbr_cell_0_293_end:
__sbr_cell_0_294:
    vmovd xmm3, edi
__sbr_cell_0_294_end:
ff_aac_sbr_apply.L6c7d:
__sbr_cell_0_295:
    vcvtss2sd xmm4, xmm2, xmm2
__sbr_cell_0_295_end:
__sbr_cell_0_296:
    vucomisd xmm0, xmm4
__sbr_cell_0_296_end:
__sbr_cell_0_297:
    jb ff_aac_sbr_apply.L9b9a
__sbr_cell_0_297_end:
__sbr_cell_0_298:
    vaddss xmm4, xmm3, xmm1
__sbr_cell_0_298_end:
__sbr_cell_0_299:
    vdivss xmm2, xmm2, xmm4
__sbr_cell_0_299_end:
__sbr_cell_0_300:
    vmovss DWORD PTR [r9+rsi*4+255000], xmm2
__sbr_cell_0_300_end:
__sbr_cell_0_301:
    vmulss xmm2, xmm3, xmm2
__sbr_cell_0_301_end:
ff_aac_sbr_apply.L6c7d_1:
__sbr_cell_0_302:
    vmovss DWORD PTR [r9+rsi*4+343768], xmm2
__sbr_cell_0_302_end:
ff_aac_sbr_apply.L6c7d_2:
__sbr_cell_0_303:
    mov edi, DWORD PTR [r9+477960]
__sbr_cell_0_303_end:
__sbr_cell_0_304:
    cmp edi, 3
__sbr_cell_0_304_end:
__sbr_cell_0_305:
    jb ff_aac_sbr_apply.L6ce0
__sbr_cell_0_305_end:
__sbr_cell_0_306:
    movzx r8d, BYTE PTR [r9+rsi*1+254967]
__sbr_cell_0_306_end:
__sbr_cell_0_307:
    mov ecx, 7
__sbr_cell_0_307_end:
__sbr_cell_0_308:
    sub ecx, r8d
__sbr_cell_0_308_end:
__sbr_cell_0_309:
    cmp r8d, 134
__sbr_cell_0_309_end:
__sbr_cell_0_310:
    jae ff_aac_sbr_apply.L6cea
__sbr_cell_0_310_end:
__sbr_cell_0_311:
    shl ecx, 23
__sbr_cell_0_311_end:
__sbr_cell_0_312:
    add ecx, 1065353216
__sbr_cell_0_312_end:
__sbr_cell_0_313:
    vmovd xmm2, ecx
__sbr_cell_0_313_end:
__sbr_cell_0_314:
    jmp ff_aac_sbr_apply.L6d09
__sbr_cell_0_314_end:
ff_aac_sbr_apply.L6ce0:
__sbr_cell_0_315:
    mov r8d, edi
__sbr_cell_0_315_end:
__sbr_cell_0_316:
    mov ecx, edi
__sbr_cell_0_316_end:
__sbr_cell_0_317:
    jmp ff_aac_sbr_apply.L6b02
__sbr_cell_0_317_end:
ff_aac_sbr_apply.L6cea:
__sbr_cell_0_318:
    vxorps xmm2, xmm2, xmm2
__sbr_cell_0_318_end:
__sbr_cell_0_319:
    cmp ecx, 4294967147
__sbr_cell_0_319_end:
__sbr_cell_0_320:
    jb ff_aac_sbr_apply.L6d09
__sbr_cell_0_320_end:
__sbr_cell_0_321:
    mov cl, 156
__sbr_cell_0_321_end:
__sbr_cell_0_322:
    sub cl, r8b
__sbr_cell_0_322_end:
__sbr_cell_0_323:
    mov r8d, 1
__sbr_cell_0_323_end:
__sbr_cell_0_324:
    shl r8d, cl
__sbr_cell_0_324_end:
__sbr_cell_0_325:
    vmovd xmm2, r8d
__sbr_cell_0_325_end:
ff_aac_sbr_apply.L6d09:
__sbr_cell_0_326:
    movzx r8d, BYTE PTR [r9+rsi*1+343735]
__sbr_cell_0_326_end:
__sbr_cell_0_327:
    mov ecx, 12
__sbr_cell_0_327_end:
__sbr_cell_0_328:
    sub ecx, r8d
__sbr_cell_0_328_end:
__sbr_cell_0_329:
    cmp r8d, 139
__sbr_cell_0_329_end:
__sbr_cell_0_330:
    jae ff_aac_sbr_apply.L6d32
__sbr_cell_0_330_end:
__sbr_cell_0_331:
    shl ecx, 23
__sbr_cell_0_331_end:
__sbr_cell_0_332:
    add ecx, 1065353216
__sbr_cell_0_332_end:
__sbr_cell_0_333:
    vmovd xmm3, ecx
__sbr_cell_0_333_end:
__sbr_cell_0_334:
    jmp ff_aac_sbr_apply.L6d51
__sbr_cell_0_334_end:
ff_aac_sbr_apply.L6d32:
__sbr_cell_0_335:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_0_335_end:
__sbr_cell_0_336:
    cmp ecx, 4294967147
__sbr_cell_0_336_end:
__sbr_cell_0_337:
    jb ff_aac_sbr_apply.L6d51
__sbr_cell_0_337_end:
__sbr_cell_0_338:
    mov cl, 161
__sbr_cell_0_338_end:
__sbr_cell_0_339:
    sub cl, r8b
__sbr_cell_0_339_end:
__sbr_cell_0_340:
    mov r8d, 1
__sbr_cell_0_340_end:
__sbr_cell_0_341:
    shl r8d, cl
__sbr_cell_0_341_end:
__sbr_cell_0_342:
    vmovd xmm3, r8d
__sbr_cell_0_342_end:
ff_aac_sbr_apply.L6d51:
__sbr_cell_0_343:
    vcvtss2sd xmm4, xmm2, xmm2
__sbr_cell_0_343_end:
__sbr_cell_0_344:
    vucomisd xmm0, xmm4
__sbr_cell_0_344_end:
__sbr_cell_0_345:
    jb ff_aac_sbr_apply.L9b9a
__sbr_cell_0_345_end:
__sbr_cell_0_346:
    vaddss xmm4, xmm3, xmm1
__sbr_cell_0_346_end:
__sbr_cell_0_347:
    vdivss xmm2, xmm2, xmm4
__sbr_cell_0_347_end:
__sbr_cell_0_348:
    vmovss DWORD PTR [r9+rsi*4+255004], xmm2
__sbr_cell_0_348_end:
__sbr_cell_0_349:
    vmulss xmm2, xmm3, xmm2
__sbr_cell_0_349_end:
ff_aac_sbr_apply.L6d51_1:
__sbr_cell_0_350:
    vmovss DWORD PTR [r9+rsi*4+343772], xmm2
__sbr_cell_0_350_end:
__sbr_cell_0_351:
    mov r8d, 3
__sbr_cell_0_351_end:
__sbr_cell_0_352:
    mov ecx, 3
__sbr_cell_0_352_end:
__sbr_cell_0_353:
    cmp edi, 3
__sbr_cell_0_353_end:
__sbr_cell_0_354:
    je ff_aac_sbr_apply.L6b02
__sbr_cell_0_354_end:
__sbr_cell_0_355:
    movzx r8d, BYTE PTR [r9+rsi*1+254968]
__sbr_cell_0_355_end:
__sbr_cell_0_356:
    mov ecx, 7
__sbr_cell_0_356_end:
__sbr_cell_0_357:
    sub ecx, r8d
__sbr_cell_0_357_end:
__sbr_cell_0_358:
    cmp r8d, 134
__sbr_cell_0_358_end:
__sbr_cell_0_359:
    jae ff_aac_sbr_apply.L6dbc
__sbr_cell_0_359_end:
__sbr_cell_0_360:
    shl ecx, 23
__sbr_cell_0_360_end:
__sbr_cell_0_361:
    add ecx, 1065353216
__sbr_cell_0_361_end:
__sbr_cell_0_362:
    vmovd xmm2, ecx
__sbr_cell_0_362_end:
__sbr_cell_0_363:
    jmp ff_aac_sbr_apply.L6ddb
__sbr_cell_0_363_end:
ff_aac_sbr_apply.L6dbc:
__sbr_cell_0_364:
    vxorps xmm2, xmm2, xmm2
__sbr_cell_0_364_end:
__sbr_cell_0_365:
    cmp ecx, 4294967147
__sbr_cell_0_365_end:
__sbr_cell_0_366:
    jb ff_aac_sbr_apply.L6ddb
__sbr_cell_0_366_end:
__sbr_cell_0_367:
    mov cl, 156
__sbr_cell_0_367_end:
__sbr_cell_0_368:
    sub cl, r8b
__sbr_cell_0_368_end:
__sbr_cell_0_369:
    mov r8d, 1
__sbr_cell_0_369_end:
__sbr_cell_0_370:
    shl r8d, cl
__sbr_cell_0_370_end:
__sbr_cell_0_371:
    vmovd xmm2, r8d
__sbr_cell_0_371_end:
ff_aac_sbr_apply.L6ddb:
__sbr_cell_0_372:
    movzx r8d, BYTE PTR [r9+rsi*1+343736]
__sbr_cell_0_372_end:
__sbr_cell_0_373:
    mov ecx, 12
__sbr_cell_0_373_end:
__sbr_cell_0_374:
    sub ecx, r8d
__sbr_cell_0_374_end:
__sbr_cell_0_375:
    cmp r8d, 139
__sbr_cell_0_375_end:
__sbr_cell_0_376:
    jae ff_aac_sbr_apply.L6e04
__sbr_cell_0_376_end:
__sbr_cell_0_377:
    shl ecx, 23
__sbr_cell_0_377_end:
__sbr_cell_0_378:
    add ecx, 1065353216
__sbr_cell_0_378_end:
__sbr_cell_0_379:
    vmovd xmm3, ecx
__sbr_cell_0_379_end:
__sbr_cell_0_380:
    jmp ff_aac_sbr_apply.L6e23
__sbr_cell_0_380_end:
ff_aac_sbr_apply.L6e04:
__sbr_cell_0_381:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_0_381_end:
__sbr_cell_0_382:
    cmp ecx, 4294967147
__sbr_cell_0_382_end:
__sbr_cell_0_383:
    jb ff_aac_sbr_apply.L6e23
__sbr_cell_0_383_end:
__sbr_cell_0_384:
    mov cl, 161
__sbr_cell_0_384_end:
__sbr_cell_0_385:
    sub cl, r8b
__sbr_cell_0_385_end:
__sbr_cell_0_386:
    mov r8d, 1
__sbr_cell_0_386_end:
__sbr_cell_0_387:
    shl r8d, cl
__sbr_cell_0_387_end:
__sbr_cell_0_388:
    vmovd xmm3, r8d
__sbr_cell_0_388_end:
ff_aac_sbr_apply.L6e23:
__sbr_cell_0_389:
    vcvtss2sd xmm4, xmm2, xmm2
__sbr_cell_0_389_end:
__sbr_cell_0_390:
    vucomisd xmm0, xmm4
__sbr_cell_0_390_end:
__sbr_cell_0_391:
    jb ff_aac_sbr_apply.L9b9a
__sbr_cell_0_391_end:
__sbr_cell_0_392:
    vaddss xmm4, xmm3, xmm1
__sbr_cell_0_392_end:
__sbr_cell_0_393:
    vdivss xmm2, xmm2, xmm4
__sbr_cell_0_393_end:
__sbr_cell_0_394:
    vmovss DWORD PTR [r9+rsi*4+255008], xmm2
__sbr_cell_0_394_end:
__sbr_cell_0_395:
    vmulss xmm2, xmm3, xmm2
__sbr_cell_0_395_end:
ff_aac_sbr_apply.L6e23_1:
__sbr_cell_0_396:
    vmovss DWORD PTR [r9+rsi*4+343776], xmm2
__sbr_cell_0_396_end:
__sbr_cell_0_397:
    mov r8d, 4
__sbr_cell_0_397_end:
__sbr_cell_0_398:
    mov ecx, 4
__sbr_cell_0_398_end:
__sbr_cell_0_399:
    cmp edi, 5
__sbr_cell_0_399_end:
__sbr_cell_0_400:
    jb ff_aac_sbr_apply.L6b02
__sbr_cell_0_400_end:
__sbr_cell_0_401:
    movzx edi, BYTE PTR [r9+rsi*1+254969]
__sbr_cell_0_401_end:
__sbr_cell_0_402:
    mov ecx, 7
__sbr_cell_0_402_end:
__sbr_cell_0_403:
    sub ecx, edi
__sbr_cell_0_403_end:
__sbr_cell_0_404:
    cmp edi, 134
__sbr_cell_0_404_end:
__sbr_cell_0_405:
    jae ff_aac_sbr_apply.L6e8c
__sbr_cell_0_405_end:
__sbr_cell_0_406:
    shl ecx, 23
__sbr_cell_0_406_end:
__sbr_cell_0_407:
    add ecx, 1065353216
__sbr_cell_0_407_end:
__sbr_cell_0_408:
    vmovd xmm2, ecx
__sbr_cell_0_408_end:
__sbr_cell_0_409:
    jmp ff_aac_sbr_apply.L6ea8
__sbr_cell_0_409_end:
ff_aac_sbr_apply.L6e8c:
__sbr_cell_0_410:
    vxorps xmm2, xmm2, xmm2
__sbr_cell_0_410_end:
__sbr_cell_0_411:
    cmp ecx, 4294967147
__sbr_cell_0_411_end:
__sbr_cell_0_412:
    jb ff_aac_sbr_apply.L6ea8
__sbr_cell_0_412_end:
__sbr_cell_0_413:
    mov cl, 156
__sbr_cell_0_413_end:
__sbr_cell_0_414:
    sub cl, dil
__sbr_cell_0_414_end:
__sbr_cell_0_415:
    mov edi, 1
__sbr_cell_0_415_end:
__sbr_cell_0_416:
    shl edi, cl
__sbr_cell_0_416_end:
__sbr_cell_0_417:
    vmovd xmm2, edi
__sbr_cell_0_417_end:
ff_aac_sbr_apply.L6ea8:
__sbr_cell_0_418:
    movzx edi, BYTE PTR [r9+rsi*1+343737]
__sbr_cell_0_418_end:
__sbr_cell_0_419:
    mov ecx, 12
__sbr_cell_0_419_end:
__sbr_cell_0_420:
    sub ecx, edi
__sbr_cell_0_420_end:
__sbr_cell_0_421:
    cmp edi, 139
__sbr_cell_0_421_end:
__sbr_cell_0_422:
    jae ff_aac_sbr_apply.L6ecf
__sbr_cell_0_422_end:
__sbr_cell_0_423:
    shl ecx, 23
__sbr_cell_0_423_end:
__sbr_cell_0_424:
    add ecx, 1065353216
__sbr_cell_0_424_end:
__sbr_cell_0_425:
    vmovd xmm3, ecx
__sbr_cell_0_425_end:
__sbr_cell_0_426:
    jmp ff_aac_sbr_apply.L6eeb
__sbr_cell_0_426_end:
ff_aac_sbr_apply.L6ecf:
__sbr_cell_0_427:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_0_427_end:
__sbr_cell_0_428:
    cmp ecx, 4294967147
__sbr_cell_0_428_end:
__sbr_cell_0_429:
    jb ff_aac_sbr_apply.L6eeb
__sbr_cell_0_429_end:
__sbr_cell_0_430:
    mov cl, 161
__sbr_cell_0_430_end:
__sbr_cell_0_431:
    sub cl, dil
__sbr_cell_0_431_end:
__sbr_cell_0_432:
    mov edi, 1
__sbr_cell_0_432_end:
__sbr_cell_0_433:
    shl edi, cl
__sbr_cell_0_433_end:
__sbr_cell_0_434:
    vmovd xmm3, edi
__sbr_cell_0_434_end:
ff_aac_sbr_apply.L6eeb:
__sbr_cell_0_435:
    vcvtss2sd xmm4, xmm2, xmm2
__sbr_cell_0_435_end:
__sbr_cell_0_436:
    vucomisd xmm0, xmm4
__sbr_cell_0_436_end:
__sbr_cell_0_437:
    jb ff_aac_sbr_apply.L9b9a
__sbr_cell_0_437_end:
__sbr_cell_0_438:
    vaddss xmm4, xmm3, xmm1
__sbr_cell_0_438_end:
__sbr_cell_0_439:
    vdivss xmm2, xmm2, xmm4
__sbr_cell_0_439_end:
__sbr_cell_0_440:
    vmovss DWORD PTR [r9+rsi*4+255012], xmm2
__sbr_cell_0_440_end:
__sbr_cell_0_441:
    vmulss xmm2, xmm3, xmm2
__sbr_cell_0_441_end:
ff_aac_sbr_apply.L6eeb_1:
__sbr_cell_0_442:
    vmovss DWORD PTR [r9+rsi*4+343780], xmm2
__sbr_cell_0_442_end:
ff_aac_sbr_apply.L6eeb_2:
__sbr_cell_0_443:
    mov r8d, DWORD PTR [r9+477960]
__sbr_cell_0_443_end:
__sbr_cell_0_444:
    mov ecx, r8d
__sbr_cell_0_444_end:
__sbr_cell_0_445:
    cmp r8d, 5
__sbr_cell_0_445_end:
__sbr_cell_0_446:
    jbe ff_aac_sbr_apply.L6b02
__sbr_cell_0_446_end:
__sbr_cell_0_447:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_447_end:
ff_aac_sbr_apply.L6f32:
__sbr_cell_0_448:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_0_448_end:
__sbr_cell_0_449:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_0_449_end:
__sbr_cell_0_450:
    lea rdx, [rip+L_str_2]
__sbr_cell_0_450_end:
__sbr_cell_0_451:
    mov esi, 16
__sbr_cell_0_451_end:
__sbr_cell_0_452:
    xor eax, eax
__sbr_cell_0_452_end:
__sbr_cell_0_453:
    call av_log
__sbr_cell_0_453_end:
ff_aac_sbr_apply.L6f32_1:
__sbr_cell_0_454:
    mov r9, QWORD PTR [rbp-56]
__sbr_cell_0_454_end:
__sbr_cell_0_455:
    mov QWORD PTR [r9+166180], 0
__sbr_cell_0_455_end:
__sbr_cell_0_456:
    mov DWORD PTR [r9+166192], 0
__sbr_cell_0_456_end:
__sbr_cell_0_457:
    mov DWORD PTR [r9+166264], 32
__sbr_cell_0_457_end:
__sbr_cell_0_458:
    mov DWORD PTR [r9+166272], 0
__sbr_cell_0_458_end:
__sbr_cell_0_459:
    mov DWORD PTR [r9+269672], 4294967295
__sbr_cell_0_459_end:
__sbr_cell_0_460:
    mov DWORD PTR [r9+180904], 4294967295
__sbr_cell_0_460_end:
__sbr_cell_0_461:
    mov DWORD PTR [r9+166204], 4294967295
__sbr_cell_0_461_end:
__sbr_cell_0_462:
    mov WORD PTR [r9+166208], 65535
__sbr_cell_0_462_end:
ff_aac_sbr_apply.L6f32_2:
__sbr_cell_0_463:
    cmp DWORD PTR [r9+166276], 0
__sbr_cell_0_463_end:
__sbr_cell_0_464:
    jne ff_aac_sbr_apply.L6825
__sbr_cell_0_464_end:
__sbr_cell_0_465:
    jmp ff_aac_sbr_apply.L676e
__sbr_cell_0_465_end:
ff_aac_sbr_apply.L6fbe:
__sbr_cell_0_466:
    mov eax, 2
__sbr_cell_0_466_end:
__sbr_cell_0_467:
    mov QWORD PTR [rbp-200], rax
__sbr_cell_0_467_end:
ff_aac_sbr_apply.L6fca:
__sbr_cell_0_468:
    lea rax, [r9+166304]
__sbr_cell_0_468_end:
__sbr_cell_0_469:
    mov QWORD PTR [rbp-88], rax
__sbr_cell_0_469_end:
__sbr_cell_0_470:
    lea rax, [r9+252848]
__sbr_cell_0_470_end:
__sbr_cell_0_471:
    mov QWORD PTR [rbp-80], rax
__sbr_cell_0_471_end:
__sbr_cell_0_472:
    lea rax, [r9+253424]
__sbr_cell_0_472_end:
__sbr_cell_0_473:
    mov QWORD PTR [rbp-72], rax
__sbr_cell_0_473_end:
__sbr_cell_0_474:
    vmovsd xmm1, QWORD PTR [rip+LCPI14_4]
__sbr_cell_0_474_end:
__sbr_cell_0_475:
    xor eax, eax
__sbr_cell_0_475_end:
__sbr_cell_0_476:
    jmp ff_aac_sbr_apply.L7044
__sbr_cell_0_476_end:
ff_aac_sbr_apply.L6ff7:
__sbr_cell_0_477:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_477_end:
ff_aac_sbr_apply.L6ffc:
__sbr_cell_0_478:
    shl ecx, 23
__sbr_cell_0_478_end:
__sbr_cell_0_479:
    add ecx, 1065353216
__sbr_cell_0_479_end:
__sbr_cell_0_480:
    mov esi, ecx
__sbr_cell_0_480_end:
ff_aac_sbr_apply.L7007:
__sbr_cell_0_481:
    mov DWORD PTR [r13+88728], esi
__sbr_cell_0_481_end:
ff_aac_sbr_apply.L700e:
__sbr_cell_0_482:
    cmp rax, 3
__sbr_cell_0_482_end:
__sbr_cell_0_483:
    jne ff_aac_sbr_apply.L9c13
__sbr_cell_0_483_end:
__sbr_cell_0_484:
    .nops 1
__sbr_cell_0_484_end:
ff_aac_sbr_apply.L7020:
__sbr_cell_0_485:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_0_485_end:
__sbr_cell_0_486:
    inc rax
__sbr_cell_0_486_end:
__sbr_cell_0_487:
    add QWORD PTR [rbp-80], 88768
__sbr_cell_0_487_end:
ff_aac_sbr_apply.L7020_1:
__sbr_cell_0_488:
    add QWORD PTR [rbp-72], 88768
__sbr_cell_0_488_end:
ff_aac_sbr_apply.L7020_2:
__sbr_cell_0_489:
    cmp rax, QWORD PTR [rbp-200]
__sbr_cell_0_489_end:
__sbr_cell_0_490:
    je ff_aac_sbr_apply.L74de
__sbr_cell_0_490_end:
ff_aac_sbr_apply.L7044:
__sbr_cell_0_491:
    mov QWORD PTR [rbp-48], rax
__sbr_cell_0_491_end:
__sbr_cell_0_492:
    imul rax, rax, 88768
__sbr_cell_0_492_end:
ff_aac_sbr_apply.L7044_1:
__sbr_cell_0_493:
    mov rcx, QWORD PTR [rbp-88]
__sbr_cell_0_493_end:
__sbr_cell_0_494:
    lea r13, [rcx+rax*1+0]
__sbr_cell_0_494_end:
__sbr_cell_0_495:
    cmp DWORD PTR [rcx+rax*1+8], 0
__sbr_cell_0_495_end:
__sbr_cell_0_496:
    je ff_aac_sbr_apply.L71e0
__sbr_cell_0_496_end:
__sbr_cell_0_497:
    mov r15d, 1
__sbr_cell_0_497_end:
__sbr_cell_0_498:
    mov r12, QWORD PTR [rbp-72]
__sbr_cell_0_498_end:
__sbr_cell_0_499:
    mov r14, QWORD PTR [rbp-80]
__sbr_cell_0_499_end:
ff_aac_sbr_apply.L7070:
__sbr_cell_0_500:
    movzx eax, BYTE PTR [r13+r15*1+12]
__sbr_cell_0_500_end:
__sbr_cell_0_501:
    cmp al, 1
__sbr_cell_0_501_end:
__sbr_cell_0_502:
    ja ff_aac_sbr_apply.L99ee
__sbr_cell_0_502_end:
__sbr_cell_0_503:
    xor ebx, ebx
__sbr_cell_0_503_end:
__sbr_cell_0_504:
    jmp ff_aac_sbr_apply.L70ca
__sbr_cell_0_504_end:
__sbr_cell_0_505:
    .nops 1
__sbr_cell_0_505_end:
ff_aac_sbr_apply.L7090:
__sbr_cell_0_506:
    xor edi, edi
__sbr_cell_0_506_end:
__sbr_cell_0_507:
    mov esi, 16
__sbr_cell_0_507_end:
__sbr_cell_0_508:
    lea rdx, [rip+L_str_33]
__sbr_cell_0_508_end:
__sbr_cell_0_509:
    xor eax, eax
__sbr_cell_0_509_end:
__sbr_cell_0_510:
    call av_log
__sbr_cell_0_510_end:
ff_aac_sbr_apply.L7090_1:
__sbr_cell_0_511:
    vmovsd xmm1, QWORD PTR [rip+LCPI14_4]
__sbr_cell_0_511_end:
__sbr_cell_0_512:
    mov r9, QWORD PTR [rbp-56]
__sbr_cell_0_512_end:
__sbr_cell_0_513:
    mov DWORD PTR [r12+rbx*4+0], 1065353216
__sbr_cell_0_513_end:
ff_aac_sbr_apply.L7090_2:
__sbr_cell_0_514:
    movzx eax, BYTE PTR [r13+r15*1+12]
__sbr_cell_0_514_end:
ff_aac_sbr_apply.L70bf:
__sbr_cell_0_515:
    inc rbx
__sbr_cell_0_515_end:
__sbr_cell_0_516:
    cmp al, 2
__sbr_cell_0_516_end:
__sbr_cell_0_517:
    jae ff_aac_sbr_apply.L99ee
__sbr_cell_0_517_end:
ff_aac_sbr_apply.L70ca:
__sbr_cell_0_518:
    movzx ecx, al
__sbr_cell_0_518_end:
__sbr_cell_0_519:
    mov ecx, DWORD PTR [r9+rcx*4+477952]
__sbr_cell_0_519_end:
__sbr_cell_0_520:
    cmp rbx, rcx
__sbr_cell_0_520_end:
__sbr_cell_0_521:
    jae ff_aac_sbr_apply.L71b0
__sbr_cell_0_521_end:
__sbr_cell_0_522:
    cmp DWORD PTR [r13+100], 0
__sbr_cell_0_522_end:
__sbr_cell_0_523:
    je ff_aac_sbr_apply.L7120
__sbr_cell_0_523_end:
__sbr_cell_0_524:
    cmp rbx, 48
__sbr_cell_0_524_end:
__sbr_cell_0_525:
    jae ff_aac_sbr_apply.L9b3b
__sbr_cell_0_525_end:
__sbr_cell_0_526:
    movzx ecx, BYTE PTR [r14+rbx*1+0]
__sbr_cell_0_526_end:
__sbr_cell_0_527:
    cmp ecx, 123
__sbr_cell_0_527_end:
__sbr_cell_0_528:
    jb ff_aac_sbr_apply.L7140
__sbr_cell_0_528_end:
__sbr_cell_0_529:
    vmovss xmm0, DWORD PTR [rip+LCPI14_0]
__sbr_cell_0_529_end:
__sbr_cell_0_530:
    vmovss DWORD PTR [r12+rbx*4+0], xmm0
__sbr_cell_0_530_end:
__sbr_cell_0_531:
    vcvtss2sd xmm0, xmm0, xmm0
__sbr_cell_0_531_end:
__sbr_cell_0_532:
    vucomisd xmm0, xmm1
__sbr_cell_0_532_end:
ff_aac_sbr_apply.L70ca_1:
__sbr_cell_0_533:
    jbe ff_aac_sbr_apply.L70bf
__sbr_cell_0_533_end:
__sbr_cell_0_534:
    jmp ff_aac_sbr_apply.L7090
__sbr_cell_0_534_end:
__sbr_cell_0_535:
    .nops 1
__sbr_cell_0_535_end:
ff_aac_sbr_apply.L7120:
__sbr_cell_0_536:
    cmp rbx, 48
__sbr_cell_0_536_end:
__sbr_cell_0_537:
    jae ff_aac_sbr_apply.L9b45
__sbr_cell_0_537_end:
__sbr_cell_0_538:
    movzx ecx, BYTE PTR [r14+rbx*1+0]
__sbr_cell_0_538_end:
__sbr_cell_0_539:
    cmp cl, 246
__sbr_cell_0_539_end:
__sbr_cell_0_540:
    jb ff_aac_sbr_apply.L7166
__sbr_cell_0_540_end:
__sbr_cell_0_541:
    vmovsd xmm0, QWORD PTR [rip+LCPI14_3]
__sbr_cell_0_541_end:
__sbr_cell_0_542:
    jmp ff_aac_sbr_apply.L717f
__sbr_cell_0_542_end:
__sbr_cell_0_543:
    .nops 1
__sbr_cell_0_543_end:
ff_aac_sbr_apply.L7140:
__sbr_cell_0_544:
    shl ecx, 23
__sbr_cell_0_544_end:
__sbr_cell_0_545:
    add ecx, 1115684864
__sbr_cell_0_545_end:
__sbr_cell_0_546:
    vmovd xmm0, ecx
__sbr_cell_0_546_end:
__sbr_cell_0_547:
    vmovd DWORD PTR [r12+rbx*4+0], xmm0
__sbr_cell_0_547_end:
__sbr_cell_0_548:
    vcvtss2sd xmm0, xmm0, xmm0
__sbr_cell_0_548_end:
__sbr_cell_0_549:
    vucomisd xmm0, xmm1
__sbr_cell_0_549_end:
__sbr_cell_0_550:
    ja ff_aac_sbr_apply.L7090
__sbr_cell_0_550_end:
__sbr_cell_0_551:
    jmp ff_aac_sbr_apply.L70bf
__sbr_cell_0_551_end:
ff_aac_sbr_apply.L7166:
__sbr_cell_0_552:
    mov edx, ecx
__sbr_cell_0_552_end:
__sbr_cell_0_553:
    shl edx, 22
__sbr_cell_0_553_end:
__sbr_cell_0_554:
    and edx, 1065353216
__sbr_cell_0_554_end:
__sbr_cell_0_555:
    add edx, 1115684864
__sbr_cell_0_555_end:
__sbr_cell_0_556:
    vmovd xmm0, edx
__sbr_cell_0_556_end:
__sbr_cell_0_557:
    vcvtss2sd xmm0, xmm0, xmm0
__sbr_cell_0_557_end:
ff_aac_sbr_apply.L717f:
__sbr_cell_0_558:
    and ecx, 1
__sbr_cell_0_558_end:
__sbr_cell_0_559:
    lea rdx, [rip+exp2_tab]
__sbr_cell_0_559_end:
__sbr_cell_0_560:
    vmulsd xmm0, xmm0, QWORD PTR [rdx+rcx*8+0]
__sbr_cell_0_560_end:
__sbr_cell_0_561:
    vcvtsd2ss xmm0, xmm0, xmm0
__sbr_cell_0_561_end:
__sbr_cell_0_562:
    vmovss DWORD PTR [r12+rbx*4+0], xmm0
__sbr_cell_0_562_end:
__sbr_cell_0_563:
    vcvtss2sd xmm0, xmm0, xmm0
__sbr_cell_0_563_end:
__sbr_cell_0_564:
    vucomisd xmm0, xmm1
__sbr_cell_0_564_end:
__sbr_cell_0_565:
    jbe ff_aac_sbr_apply.L70bf
__sbr_cell_0_565_end:
__sbr_cell_0_566:
    jmp ff_aac_sbr_apply.L7090
__sbr_cell_0_566_end:
__sbr_cell_0_567:
    .nops 1
__sbr_cell_0_567_end:
ff_aac_sbr_apply.L71b0:
__sbr_cell_0_568:
    mov eax, DWORD PTR [r13+8]
__sbr_cell_0_568_end:
__sbr_cell_0_569:
    cmp r15, rax
__sbr_cell_0_569_end:
__sbr_cell_0_570:
    jae ff_aac_sbr_apply.L71e0
__sbr_cell_0_570_end:
__sbr_cell_0_571:
    inc r15
__sbr_cell_0_571_end:
__sbr_cell_0_572:
    add r14, 48
__sbr_cell_0_572_end:
__sbr_cell_0_573:
    add r12, 192
__sbr_cell_0_573_end:
__sbr_cell_0_574:
    cmp r15, 9
__sbr_cell_0_574_end:
__sbr_cell_0_575:
    jne ff_aac_sbr_apply.L7070
__sbr_cell_0_575_end:
__sbr_cell_0_576:
    jmp ff_aac_sbr_apply.L99f3
__sbr_cell_0_576_end:
__sbr_cell_0_577:
    .nops 1
__sbr_cell_0_577_end:
ff_aac_sbr_apply.L71e0:
__sbr_cell_0_578:
    mov eax, DWORD PTR [r13+24]
__sbr_cell_0_578_end:
__sbr_cell_0_579:
    test rax, rax
__sbr_cell_0_579_end:
__sbr_cell_0_580:
    mov r14d, 0
__sbr_cell_0_580_end:
__sbr_cell_0_581:
    je ff_aac_sbr_apply.L7020
__sbr_cell_0_581_end:
__sbr_cell_0_582:
    mov edx, DWORD PTR [r9+477960]
__sbr_cell_0_582_end:
__sbr_cell_0_583:
    test edx, edx
__sbr_cell_0_583_end:
__sbr_cell_0_584:
    je ff_aac_sbr_apply.L7020
__sbr_cell_0_584_end:
__sbr_cell_0_585:
    movzx esi, BYTE PTR [r13+88661]
__sbr_cell_0_585_end:
__sbr_cell_0_586:
    mov ecx, 6
__sbr_cell_0_586_end:
__sbr_cell_0_587:
    sub ecx, esi
__sbr_cell_0_587_end:
__sbr_cell_0_588:
    cmp esi, 133
__sbr_cell_0_588_end:
__sbr_cell_0_589:
    jae ff_aac_sbr_apply.L7226
__sbr_cell_0_589_end:
__sbr_cell_0_590:
    shl ecx, 23
__sbr_cell_0_590_end:
__sbr_cell_0_591:
    add ecx, 1065353216
__sbr_cell_0_591_end:
__sbr_cell_0_592:
    mov edi, ecx
__sbr_cell_0_592_end:
ff_aac_sbr_apply.L71e0_1:
__sbr_cell_0_593:
    jmp ff_aac_sbr_apply.L723c
__sbr_cell_0_593_end:
ff_aac_sbr_apply.L7226:
__sbr_cell_0_594:
    xor edi, edi
__sbr_cell_0_594_end:
__sbr_cell_0_595:
    cmp ecx, 4294967147
__sbr_cell_0_595_end:
__sbr_cell_0_596:
    jb ff_aac_sbr_apply.L723c
__sbr_cell_0_596_end:
__sbr_cell_0_597:
    mov cl, 155
__sbr_cell_0_597_end:
__sbr_cell_0_598:
    sub cl, sil
__sbr_cell_0_598_end:
__sbr_cell_0_599:
    mov edi, 1
__sbr_cell_0_599_end:
__sbr_cell_0_600:
    shl edi, cl
__sbr_cell_0_600_end:
ff_aac_sbr_apply.L723c:
__sbr_cell_0_601:
    mov DWORD PTR [r13+88692], edi
__sbr_cell_0_601_end:
__sbr_cell_0_602:
    cmp edx, 1
__sbr_cell_0_602_end:
__sbr_cell_0_603:
    je ff_aac_sbr_apply.L7370
__sbr_cell_0_603_end:
ff_aac_sbr_apply.L723c_1:
__sbr_cell_0_604:
    movzx esi, BYTE PTR [r13+88662]
__sbr_cell_0_604_end:
__sbr_cell_0_605:
    mov ecx, 6
__sbr_cell_0_605_end:
__sbr_cell_0_606:
    sub ecx, esi
__sbr_cell_0_606_end:
__sbr_cell_0_607:
    cmp esi, 133
__sbr_cell_0_607_end:
__sbr_cell_0_608:
    jae ff_aac_sbr_apply.L7270
__sbr_cell_0_608_end:
__sbr_cell_0_609:
    shl ecx, 23
__sbr_cell_0_609_end:
__sbr_cell_0_610:
    add ecx, 1065353216
__sbr_cell_0_610_end:
__sbr_cell_0_611:
    mov edi, ecx
__sbr_cell_0_611_end:
__sbr_cell_0_612:
    jmp ff_aac_sbr_apply.L7286
__sbr_cell_0_612_end:
ff_aac_sbr_apply.L7270:
__sbr_cell_0_613:
    xor edi, edi
__sbr_cell_0_613_end:
__sbr_cell_0_614:
    cmp ecx, 4294967147
__sbr_cell_0_614_end:
__sbr_cell_0_615:
    jb ff_aac_sbr_apply.L7286
__sbr_cell_0_615_end:
__sbr_cell_0_616:
    mov cl, 155
__sbr_cell_0_616_end:
__sbr_cell_0_617:
    sub cl, sil
__sbr_cell_0_617_end:
__sbr_cell_0_618:
    mov edi, 1
__sbr_cell_0_618_end:
__sbr_cell_0_619:
    shl edi, cl
__sbr_cell_0_619_end:
ff_aac_sbr_apply.L7286:
__sbr_cell_0_620:
    mov DWORD PTR [r13+88696], edi
__sbr_cell_0_620_end:
__sbr_cell_0_621:
    cmp edx, 3
__sbr_cell_0_621_end:
__sbr_cell_0_622:
    jb ff_aac_sbr_apply.L7370
__sbr_cell_0_622_end:
ff_aac_sbr_apply.L7286_1:
__sbr_cell_0_623:
    movzx esi, BYTE PTR [r13+88663]
__sbr_cell_0_623_end:
__sbr_cell_0_624:
    mov ecx, 6
__sbr_cell_0_624_end:
__sbr_cell_0_625:
    sub ecx, esi
__sbr_cell_0_625_end:
__sbr_cell_0_626:
    cmp esi, 133
__sbr_cell_0_626_end:
__sbr_cell_0_627:
    jae ff_aac_sbr_apply.L72ba
__sbr_cell_0_627_end:
__sbr_cell_0_628:
    shl ecx, 23
__sbr_cell_0_628_end:
__sbr_cell_0_629:
    add ecx, 1065353216
__sbr_cell_0_629_end:
__sbr_cell_0_630:
    mov edi, ecx
__sbr_cell_0_630_end:
__sbr_cell_0_631:
    jmp ff_aac_sbr_apply.L72d0
__sbr_cell_0_631_end:
ff_aac_sbr_apply.L72ba:
__sbr_cell_0_632:
    xor edi, edi
__sbr_cell_0_632_end:
__sbr_cell_0_633:
    cmp ecx, 4294967147
__sbr_cell_0_633_end:
__sbr_cell_0_634:
    jb ff_aac_sbr_apply.L72d0
__sbr_cell_0_634_end:
__sbr_cell_0_635:
    mov cl, 155
__sbr_cell_0_635_end:
__sbr_cell_0_636:
    sub cl, sil
__sbr_cell_0_636_end:
__sbr_cell_0_637:
    mov edi, 1
__sbr_cell_0_637_end:
__sbr_cell_0_638:
    shl edi, cl
__sbr_cell_0_638_end:
ff_aac_sbr_apply.L72d0:
__sbr_cell_0_639:
    mov DWORD PTR [r13+88700], edi
__sbr_cell_0_639_end:
__sbr_cell_0_640:
    cmp edx, 3
__sbr_cell_0_640_end:
__sbr_cell_0_641:
    je ff_aac_sbr_apply.L7370
__sbr_cell_0_641_end:
ff_aac_sbr_apply.L72d0_1:
__sbr_cell_0_642:
    movzx esi, BYTE PTR [r13+88664]
__sbr_cell_0_642_end:
__sbr_cell_0_643:
    mov ecx, 6
__sbr_cell_0_643_end:
__sbr_cell_0_644:
    sub ecx, esi
__sbr_cell_0_644_end:
__sbr_cell_0_645:
    cmp esi, 133
__sbr_cell_0_645_end:
__sbr_cell_0_646:
    jae ff_aac_sbr_apply.L7304
__sbr_cell_0_646_end:
__sbr_cell_0_647:
    shl ecx, 23
__sbr_cell_0_647_end:
__sbr_cell_0_648:
    add ecx, 1065353216
__sbr_cell_0_648_end:
__sbr_cell_0_649:
    mov edi, ecx
__sbr_cell_0_649_end:
__sbr_cell_0_650:
    jmp ff_aac_sbr_apply.L731a
__sbr_cell_0_650_end:
ff_aac_sbr_apply.L7304:
__sbr_cell_0_651:
    xor edi, edi
__sbr_cell_0_651_end:
__sbr_cell_0_652:
    cmp ecx, 4294967147
__sbr_cell_0_652_end:
__sbr_cell_0_653:
    jb ff_aac_sbr_apply.L731a
__sbr_cell_0_653_end:
__sbr_cell_0_654:
    mov cl, 155
__sbr_cell_0_654_end:
__sbr_cell_0_655:
    sub cl, sil
__sbr_cell_0_655_end:
__sbr_cell_0_656:
    mov edi, 1
__sbr_cell_0_656_end:
__sbr_cell_0_657:
    shl edi, cl
__sbr_cell_0_657_end:
ff_aac_sbr_apply.L731a:
__sbr_cell_0_658:
    mov DWORD PTR [r13+88704], edi
__sbr_cell_0_658_end:
__sbr_cell_0_659:
    cmp edx, 5
__sbr_cell_0_659_end:
__sbr_cell_0_660:
    jb ff_aac_sbr_apply.L7370
__sbr_cell_0_660_end:
ff_aac_sbr_apply.L731a_1:
__sbr_cell_0_661:
    movzx esi, BYTE PTR [r13+88665]
__sbr_cell_0_661_end:
__sbr_cell_0_662:
    mov ecx, 6
__sbr_cell_0_662_end:
__sbr_cell_0_663:
    sub ecx, esi
__sbr_cell_0_663_end:
__sbr_cell_0_664:
    cmp esi, 133
__sbr_cell_0_664_end:
__sbr_cell_0_665:
    jae ff_aac_sbr_apply.L734a
__sbr_cell_0_665_end:
__sbr_cell_0_666:
    shl ecx, 23
__sbr_cell_0_666_end:
__sbr_cell_0_667:
    add ecx, 1065353216
__sbr_cell_0_667_end:
__sbr_cell_0_668:
    mov edi, ecx
__sbr_cell_0_668_end:
__sbr_cell_0_669:
    jmp ff_aac_sbr_apply.L7360
__sbr_cell_0_669_end:
ff_aac_sbr_apply.L734a:
__sbr_cell_0_670:
    xor edi, edi
__sbr_cell_0_670_end:
__sbr_cell_0_671:
    cmp ecx, 4294967147
__sbr_cell_0_671_end:
__sbr_cell_0_672:
    jb ff_aac_sbr_apply.L7360
__sbr_cell_0_672_end:
__sbr_cell_0_673:
    mov cl, 155
__sbr_cell_0_673_end:
__sbr_cell_0_674:
    sub cl, sil
__sbr_cell_0_674_end:
__sbr_cell_0_675:
    mov edi, 1
__sbr_cell_0_675_end:
__sbr_cell_0_676:
    shl edi, cl
__sbr_cell_0_676_end:
ff_aac_sbr_apply.L7360:
__sbr_cell_0_677:
    mov DWORD PTR [r13+88708], edi
__sbr_cell_0_677_end:
__sbr_cell_0_678:
    cmp edx, 5
__sbr_cell_0_678_end:
__sbr_cell_0_679:
    jne ff_aac_sbr_apply.L9c22
__sbr_cell_0_679_end:
ff_aac_sbr_apply.L7370:
__sbr_cell_0_680:
    inc rax
__sbr_cell_0_680_end:
__sbr_cell_0_681:
    cmp rax, 2
__sbr_cell_0_681_end:
__sbr_cell_0_682:
    je ff_aac_sbr_apply.L7020
__sbr_cell_0_682_end:
__sbr_cell_0_683:
    movzx esi, BYTE PTR [r13+88666]
__sbr_cell_0_683_end:
__sbr_cell_0_684:
    mov ecx, 6
__sbr_cell_0_684_end:
__sbr_cell_0_685:
    sub ecx, esi
__sbr_cell_0_685_end:
__sbr_cell_0_686:
    cmp esi, 133
__sbr_cell_0_686_end:
__sbr_cell_0_687:
    jae ff_aac_sbr_apply.L73a1
__sbr_cell_0_687_end:
__sbr_cell_0_688:
    shl ecx, 23
__sbr_cell_0_688_end:
__sbr_cell_0_689:
    add ecx, 1065353216
__sbr_cell_0_689_end:
__sbr_cell_0_690:
    mov edi, ecx
__sbr_cell_0_690_end:
__sbr_cell_0_691:
    jmp ff_aac_sbr_apply.L73b7
__sbr_cell_0_691_end:
ff_aac_sbr_apply.L73a1:
__sbr_cell_0_692:
    xor edi, edi
__sbr_cell_0_692_end:
__sbr_cell_0_693:
    cmp ecx, 4294967147
__sbr_cell_0_693_end:
__sbr_cell_0_694:
    jb ff_aac_sbr_apply.L73b7
__sbr_cell_0_694_end:
__sbr_cell_0_695:
    mov cl, 155
__sbr_cell_0_695_end:
__sbr_cell_0_696:
    sub cl, sil
__sbr_cell_0_696_end:
__sbr_cell_0_697:
    mov edi, 1
__sbr_cell_0_697_end:
__sbr_cell_0_698:
    shl edi, cl
__sbr_cell_0_698_end:
ff_aac_sbr_apply.L73b7:
__sbr_cell_0_699:
    mov DWORD PTR [r13+88712], edi
__sbr_cell_0_699_end:
__sbr_cell_0_700:
    cmp edx, 1
__sbr_cell_0_700_end:
__sbr_cell_0_701:
    je ff_aac_sbr_apply.L700e
__sbr_cell_0_701_end:
ff_aac_sbr_apply.L73b7_1:
__sbr_cell_0_702:
    movzx esi, BYTE PTR [r13+88667]
__sbr_cell_0_702_end:
__sbr_cell_0_703:
    mov ecx, 6
__sbr_cell_0_703_end:
__sbr_cell_0_704:
    sub ecx, esi
__sbr_cell_0_704_end:
__sbr_cell_0_705:
    cmp esi, 133
__sbr_cell_0_705_end:
__sbr_cell_0_706:
    jae ff_aac_sbr_apply.L73eb
__sbr_cell_0_706_end:
__sbr_cell_0_707:
    shl ecx, 23
__sbr_cell_0_707_end:
__sbr_cell_0_708:
    add ecx, 1065353216
__sbr_cell_0_708_end:
__sbr_cell_0_709:
    mov edi, ecx
__sbr_cell_0_709_end:
__sbr_cell_0_710:
    jmp ff_aac_sbr_apply.L7401
__sbr_cell_0_710_end:
ff_aac_sbr_apply.L73eb:
__sbr_cell_0_711:
    xor edi, edi
__sbr_cell_0_711_end:
__sbr_cell_0_712:
    cmp ecx, 4294967147
__sbr_cell_0_712_end:
__sbr_cell_0_713:
    jb ff_aac_sbr_apply.L7401
__sbr_cell_0_713_end:
__sbr_cell_0_714:
    mov cl, 155
__sbr_cell_0_714_end:
__sbr_cell_0_715:
    sub cl, sil
__sbr_cell_0_715_end:
__sbr_cell_0_716:
    mov edi, 1
__sbr_cell_0_716_end:
__sbr_cell_0_717:
    shl edi, cl
__sbr_cell_0_717_end:
ff_aac_sbr_apply.L7401:
__sbr_cell_0_718:
    mov DWORD PTR [r13+88716], edi
__sbr_cell_0_718_end:
__sbr_cell_0_719:
    cmp edx, 3
__sbr_cell_0_719_end:
__sbr_cell_0_720:
    jb ff_aac_sbr_apply.L700e
__sbr_cell_0_720_end:
ff_aac_sbr_apply.L7401_1:
__sbr_cell_0_721:
    movzx esi, BYTE PTR [r13+88668]
__sbr_cell_0_721_end:
__sbr_cell_0_722:
    mov ecx, 6
__sbr_cell_0_722_end:
__sbr_cell_0_723:
    sub ecx, esi
__sbr_cell_0_723_end:
__sbr_cell_0_724:
    cmp esi, 133
__sbr_cell_0_724_end:
__sbr_cell_0_725:
    jae ff_aac_sbr_apply.L7435
__sbr_cell_0_725_end:
__sbr_cell_0_726:
    shl ecx, 23
__sbr_cell_0_726_end:
__sbr_cell_0_727:
    add ecx, 1065353216
__sbr_cell_0_727_end:
__sbr_cell_0_728:
    mov edi, ecx
__sbr_cell_0_728_end:
__sbr_cell_0_729:
    jmp ff_aac_sbr_apply.L744b
__sbr_cell_0_729_end:
ff_aac_sbr_apply.L7435:
__sbr_cell_0_730:
    xor edi, edi
__sbr_cell_0_730_end:
__sbr_cell_0_731:
    cmp ecx, 4294967147
__sbr_cell_0_731_end:
__sbr_cell_0_732:
    jb ff_aac_sbr_apply.L744b
__sbr_cell_0_732_end:
__sbr_cell_0_733:
    mov cl, 155
__sbr_cell_0_733_end:
__sbr_cell_0_734:
    sub cl, sil
__sbr_cell_0_734_end:
__sbr_cell_0_735:
    mov edi, 1
__sbr_cell_0_735_end:
__sbr_cell_0_736:
    shl edi, cl
__sbr_cell_0_736_end:
ff_aac_sbr_apply.L744b:
__sbr_cell_0_737:
    mov DWORD PTR [r13+88720], edi
__sbr_cell_0_737_end:
__sbr_cell_0_738:
    cmp edx, 3
__sbr_cell_0_738_end:
__sbr_cell_0_739:
    je ff_aac_sbr_apply.L700e
__sbr_cell_0_739_end:
ff_aac_sbr_apply.L744b_1:
__sbr_cell_0_740:
    movzx esi, BYTE PTR [r13+88669]
__sbr_cell_0_740_end:
__sbr_cell_0_741:
    mov ecx, 6
__sbr_cell_0_741_end:
__sbr_cell_0_742:
    sub ecx, esi
__sbr_cell_0_742_end:
__sbr_cell_0_743:
    cmp esi, 133
__sbr_cell_0_743_end:
__sbr_cell_0_744:
    jae ff_aac_sbr_apply.L747f
__sbr_cell_0_744_end:
__sbr_cell_0_745:
    shl ecx, 23
__sbr_cell_0_745_end:
__sbr_cell_0_746:
    add ecx, 1065353216
__sbr_cell_0_746_end:
__sbr_cell_0_747:
    mov edi, ecx
__sbr_cell_0_747_end:
__sbr_cell_0_748:
    jmp ff_aac_sbr_apply.L7495
__sbr_cell_0_748_end:
ff_aac_sbr_apply.L747f:
__sbr_cell_0_749:
    xor edi, edi
__sbr_cell_0_749_end:
__sbr_cell_0_750:
    cmp ecx, 4294967147
__sbr_cell_0_750_end:
__sbr_cell_0_751:
    jb ff_aac_sbr_apply.L7495
__sbr_cell_0_751_end:
__sbr_cell_0_752:
    mov cl, 155
__sbr_cell_0_752_end:
__sbr_cell_0_753:
    sub cl, sil
__sbr_cell_0_753_end:
__sbr_cell_0_754:
    mov edi, 1
__sbr_cell_0_754_end:
__sbr_cell_0_755:
    shl edi, cl
__sbr_cell_0_755_end:
ff_aac_sbr_apply.L7495:
__sbr_cell_0_756:
    mov DWORD PTR [r13+88724], edi
__sbr_cell_0_756_end:
__sbr_cell_0_757:
    cmp edx, 5
__sbr_cell_0_757_end:
__sbr_cell_0_758:
    jb ff_aac_sbr_apply.L700e
__sbr_cell_0_758_end:
ff_aac_sbr_apply.L7495_1:
__sbr_cell_0_759:
    movzx edx, BYTE PTR [r13+88670]
__sbr_cell_0_759_end:
__sbr_cell_0_760:
    mov ecx, 6
__sbr_cell_0_760_end:
__sbr_cell_0_761:
    sub ecx, edx
__sbr_cell_0_761_end:
__sbr_cell_0_762:
    cmp edx, 133
__sbr_cell_0_762_end:
__sbr_cell_0_763:
    jb ff_aac_sbr_apply.L6ffc
__sbr_cell_0_763_end:
__sbr_cell_0_764:
    xor esi, esi
__sbr_cell_0_764_end:
__sbr_cell_0_765:
    cmp ecx, 4294967147
__sbr_cell_0_765_end:
__sbr_cell_0_766:
    jb ff_aac_sbr_apply.L7007
__sbr_cell_0_766_end:
__sbr_cell_0_767:
    mov cl, 155
__sbr_cell_0_767_end:
__sbr_cell_0_768:
    sub cl, dl
__sbr_cell_0_768_end:
__sbr_cell_0_769:
    mov esi, 1
__sbr_cell_0_769_end:
__sbr_cell_0_770:
    shl esi, cl
__sbr_cell_0_770_end:
__sbr_cell_0_771:
    jmp ff_aac_sbr_apply.L7007
__sbr_cell_0_771_end:
ff_aac_sbr_apply.L74de:
__sbr_cell_0_772:
    mov DWORD PTR [r9+166184], 0
__sbr_cell_0_772_end:
ff_aac_sbr_apply.L74e9:
__sbr_cell_0_773:
    lea rax, [rip+_GLOBAL_OFFSET_TABLE_]
__sbr_cell_0_773_end:
__sbr_cell_0_774:
    lea rcx, [r9+166176]
__sbr_cell_0_774_end:
__sbr_cell_0_775:
    mov QWORD PTR [rbp-176], rcx
__sbr_cell_0_775_end:
ff_aac_sbr_apply.L74e9_1:
__sbr_cell_0_776:
    movzx ecx, BYTE PTR [rbp-240]
__sbr_cell_0_776_end:
__sbr_cell_0_777:
    mov r14b, cl
__sbr_cell_0_777_end:
__sbr_cell_0_778:
    mov QWORD PTR [rbp-336], r14
__sbr_cell_0_778_end:
__sbr_cell_0_779:
    lea rcx, [r9+559872]
__sbr_cell_0_779_end:
__sbr_cell_0_780:
    mov QWORD PTR [rbp-288], rcx
__sbr_cell_0_780_end:
__sbr_cell_0_781:
    lea rcx, [r9+166304]
__sbr_cell_0_781_end:
__sbr_cell_0_782:
    mov QWORD PTR [rbp-312], rcx
__sbr_cell_0_782_end:
__sbr_cell_0_783:
    lea r12, [r9+558560]
__sbr_cell_0_783_end:
__sbr_cell_0_784:
    lea r13, [r9+558816]
__sbr_cell_0_784_end:
__sbr_cell_0_785:
    lea rcx, [r9+478304]
__sbr_cell_0_785_end:
__sbr_cell_0_786:
    mov QWORD PTR [rbp-192], rcx
__sbr_cell_0_786_end:
__sbr_cell_0_787:
    lea rcx, [r9+547936]
__sbr_cell_0_787_end:
__sbr_cell_0_788:
    mov QWORD PTR [rbp-328], rcx
__sbr_cell_0_788_end:
__sbr_cell_0_789:
    lea rcx, [r9+548448]
__sbr_cell_0_789_end:
__sbr_cell_0_790:
    mov QWORD PTR [rbp-320], rcx
__sbr_cell_0_790_end:
ff_aac_sbr_apply.L74e9_2:
__sbr_cell_0_791:
    lea rcx, [r9+488544]
__sbr_cell_0_791_end:
__sbr_cell_0_792:
    mov QWORD PTR [rbp-184], rcx
__sbr_cell_0_792_end:
__sbr_cell_0_793:
    lea rcx, [r9+478116]
__sbr_cell_0_793_end:
__sbr_cell_0_794:
    mov QWORD PTR [rbp-440], rcx
__sbr_cell_0_794_end:
__sbr_cell_0_795:
    lea rcx, [r9+478066]
__sbr_cell_0_795_end:
__sbr_cell_0_796:
    mov QWORD PTR [rbp-432], rcx
__sbr_cell_0_796_end:
__sbr_cell_0_797:
    movabs r15, offset sbr_qmf_window_ds@GOTOFF
__sbr_cell_0_797_end:
__sbr_cell_0_798:
    add r15, rax
__sbr_cell_0_798_end:
__sbr_cell_0_799:
    lea rax, [r9+548960]
__sbr_cell_0_799_end:
__sbr_cell_0_800:
    mov QWORD PTR [rbp-208], rax
__sbr_cell_0_800_end:
__sbr_cell_0_801:
    lea rax, [r9+550496]
__sbr_cell_0_801_end:
__sbr_cell_0_802:
    mov QWORD PTR [rbp-392], rax
__sbr_cell_0_802_end:
__sbr_cell_0_803:
    lea rax, [r9+552032]
__sbr_cell_0_803_end:
__sbr_cell_0_804:
    mov QWORD PTR [rbp-424], rax
__sbr_cell_0_804_end:
__sbr_cell_0_805:
    lea rax, [r9+166204]
__sbr_cell_0_805_end:
ff_aac_sbr_apply.L74e9_3:
__sbr_cell_0_806:
    mov QWORD PTR [rbp-360], rax
__sbr_cell_0_806_end:
__sbr_cell_0_807:
    lea rax, [r9+552416]
__sbr_cell_0_807_end:
__sbr_cell_0_808:
    mov QWORD PTR [rbp-376], rax
__sbr_cell_0_808_end:
__sbr_cell_0_809:
    lea rax, [r9+553952]
__sbr_cell_0_809_end:
__sbr_cell_0_810:
    mov QWORD PTR [rbp-264], rax
__sbr_cell_0_810_end:
__sbr_cell_0_811:
    lea rax, [r9+555488]
__sbr_cell_0_811_end:
__sbr_cell_0_812:
    mov QWORD PTR [rbp-368], rax
__sbr_cell_0_812_end:
__sbr_cell_0_813:
    lea rax, [r9+557024]
__sbr_cell_0_813_end:
__sbr_cell_0_814:
    mov QWORD PTR [rbp-256], rax
__sbr_cell_0_814_end:
__sbr_cell_0_815:
    lea rax, [r9+509024]
__sbr_cell_0_815_end:
__sbr_cell_0_816:
    mov QWORD PTR [rbp-168], rax
__sbr_cell_0_816_end:
__sbr_cell_0_817:
    lea rax, [r9+478120]
__sbr_cell_0_817_end:
__sbr_cell_0_818:
    mov QWORD PTR [rbp-408], rax
__sbr_cell_0_818_end:
__sbr_cell_0_819:
    lea rax, [r9+166354]
__sbr_cell_0_819_end:
__sbr_cell_0_820:
    mov QWORD PTR [rbp-384], rax
__sbr_cell_0_820_end:
ff_aac_sbr_apply.L74e9_4:
__sbr_cell_0_821:
    lea rax, [r9+488880]
__sbr_cell_0_821_end:
__sbr_cell_0_822:
    mov QWORD PTR [rbp-112], rax
__sbr_cell_0_822_end:
__sbr_cell_0_823:
    lea rax, [r9+488560]
__sbr_cell_0_823_end:
__sbr_cell_0_824:
    mov QWORD PTR [rbp-400], rax
__sbr_cell_0_824_end:
__sbr_cell_0_825:
    lea rax, [r9+252416]
__sbr_cell_0_825_end:
__sbr_cell_0_826:
    mov QWORD PTR [rbp-352], rax
__sbr_cell_0_826_end:
__sbr_cell_0_827:
    lea rax, [r9+557028]
__sbr_cell_0_827_end:
__sbr_cell_0_828:
    mov QWORD PTR [rbp-344], rax
__sbr_cell_0_828_end:
__sbr_cell_0_829:
    mov cl, 1
__sbr_cell_0_829_end:
__sbr_cell_0_830:
    xor edx, edx
__sbr_cell_0_830_end:
__sbr_cell_0_831:
    mov QWORD PTR [rbp-200], r13
__sbr_cell_0_831_end:
__sbr_cell_0_832:
    mov QWORD PTR [rbp-240], r15
__sbr_cell_0_832_end:
__sbr_cell_0_833:
    mov QWORD PTR [rbp-280], r12
__sbr_cell_0_833_end:
ff_aac_sbr_apply.L7682:
__sbr_cell_0_834:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_0_834_end:
__sbr_cell_0_835:
    mov rax, QWORD PTR [rax+9552]
__sbr_cell_0_835_end:
__sbr_cell_0_836:
    mov QWORD PTR [rbp-48], rax
__sbr_cell_0_836_end:
__sbr_cell_0_837:
    mov r14, r12
__sbr_cell_0_837_end:
ff_aac_sbr_apply.L7682_1:
__sbr_cell_0_838:
    mov rax, QWORD PTR [r9+559840]
__sbr_cell_0_838_end:
__sbr_cell_0_839:
    mov QWORD PTR [rbp-88], rax
__sbr_cell_0_839_end:
ff_aac_sbr_apply.L7682_2:
__sbr_cell_0_840:
    mov rax, QWORD PTR [r9+559848]
__sbr_cell_0_840_end:
__sbr_cell_0_841:
    mov QWORD PTR [rbp-80], rax
__sbr_cell_0_841_end:
__sbr_cell_0_842:
    mov DWORD PTR [rbp-248], ecx
__sbr_cell_0_842_end:
__sbr_cell_0_843:
    test cl, 1
__sbr_cell_0_843_end:
ff_aac_sbr_apply.L7682_3:
__sbr_cell_0_844:
    mov rax, QWORD PTR [rbp-296]
__sbr_cell_0_844_end:
__sbr_cell_0_845:
    cmovne rax, QWORD PTR [rbp-304]
__sbr_cell_0_845_end:
__sbr_cell_0_846:
    mov QWORD PTR [rbp-104], rax
__sbr_cell_0_846_end:
__sbr_cell_0_847:
    mov QWORD PTR [rbp-416], rdx
__sbr_cell_0_847_end:
__sbr_cell_0_848:
    imul r13, rdx, 88768
__sbr_cell_0_848_end:
ff_aac_sbr_apply.L7682_4:
__sbr_cell_0_849:
    mov rcx, QWORD PTR [rbp-312]
__sbr_cell_0_849_end:
__sbr_cell_0_850:
    lea rax, [rcx+r13*1+0]
__sbr_cell_0_850_end:
__sbr_cell_0_851:
    mov QWORD PTR [rbp-72], rax
__sbr_cell_0_851_end:
__sbr_cell_0_852:
    lea rdi, [rcx+r13*1+0]
__sbr_cell_0_852_end:
__sbr_cell_0_853:
    add rdi, 9344
__sbr_cell_0_853_end:
__sbr_cell_0_854:
    lea rax, [rcx+r13*1+14624]
__sbr_cell_0_854_end:
__sbr_cell_0_855:
    mov QWORD PTR [rbp-120], rax
__sbr_cell_0_855_end:
ff_aac_sbr_apply.L7682_5:
__sbr_cell_0_856:
    movsxd r15, DWORD PTR [rcx+r13*1+31008]
__sbr_cell_0_856_end:
__sbr_cell_0_857:
    lea rsi, [rcx+r13*1+13440]
__sbr_cell_0_857_end:
__sbr_cell_0_858:
    mov edx, 1152
__sbr_cell_0_858_end:
__sbr_cell_0_859:
    mov r12, rdi
__sbr_cell_0_859_end:
__sbr_cell_0_860:
    mov rbx, r9
__sbr_cell_0_860_end:
__sbr_cell_0_861:
    call memcpy
__sbr_cell_0_861_end:
ff_aac_sbr_apply.L7682_6:
__sbr_cell_0_862:
    mov QWORD PTR [rbp-152], r13
__sbr_cell_0_862_end:
ff_aac_sbr_apply.L7682_7:
__sbr_cell_0_863:
    mov rax, QWORD PTR [rbp-312]
__sbr_cell_0_863_end:
__sbr_cell_0_864:
    lea rdi, [rax+r13*1+0]
__sbr_cell_0_864_end:
__sbr_cell_0_865:
    add rdi, 10496
__sbr_cell_0_865_end:
__sbr_cell_0_866:
    mov edx, 4096
__sbr_cell_0_866_end:
__sbr_cell_0_867:
    mov rsi, QWORD PTR [rbp-104]
__sbr_cell_0_867_end:
__sbr_cell_0_868:
    call memcpy
__sbr_cell_0_868_end:
ff_aac_sbr_apply.L7682_8:
__sbr_cell_0_869:
    shl r15, 13
__sbr_cell_0_869_end:
__sbr_cell_0_870:
    add r15, QWORD PTR [rbp-120]
__sbr_cell_0_870_end:
__sbr_cell_0_871:
    xor r13d, r13d
__sbr_cell_0_871_end:
__sbr_cell_0_872:
    .nops 1
__sbr_cell_0_872_end:
ff_aac_sbr_apply.L7750:
__sbr_cell_0_873:
    lea rdx, [r12+r13*1+0]
__sbr_cell_0_873_end:
__sbr_cell_0_874:
    mov rdi, r14
__sbr_cell_0_874_end:
__sbr_cell_0_875:
    mov rsi, QWORD PTR [rbp-240]
__sbr_cell_0_875_end:
__sbr_cell_0_876:
    mov ecx, 320
__sbr_cell_0_876_end:
__sbr_cell_0_877:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_0_877_end:
__sbr_cell_0_878:
    call QWORD PTR [rax+56]
__sbr_cell_0_878_end:
ff_aac_sbr_apply.L7750_1:
__sbr_cell_0_879:
    mov rdi, r14
__sbr_cell_0_879_end:
__sbr_cell_0_880:
    call QWORD PTR [rbx+559872]
__sbr_cell_0_880_end:
ff_aac_sbr_apply.L7750_2:
__sbr_cell_0_881:
    mov rdi, r14
__sbr_cell_0_881_end:
__sbr_cell_0_882:
    call QWORD PTR [rbx+559896]
__sbr_cell_0_882_end:
ff_aac_sbr_apply.L7750_3:
__sbr_cell_0_883:
    mov ecx, 4
__sbr_cell_0_883_end:
__sbr_cell_0_884:
    mov rdi, QWORD PTR [rbp-88]
__sbr_cell_0_884_end:
__sbr_cell_0_885:
    mov rsi, r14
__sbr_cell_0_885_end:
__sbr_cell_0_886:
    mov rdx, QWORD PTR [rbp-200]
__sbr_cell_0_886_end:
__sbr_cell_0_887:
    call QWORD PTR [rbp-80]
__sbr_cell_0_887_end:
ff_aac_sbr_apply.L7750_4:
__sbr_cell_0_888:
    mov rdi, r15
__sbr_cell_0_888_end:
__sbr_cell_0_889:
    mov rsi, r14
__sbr_cell_0_889_end:
__sbr_cell_0_890:
    call QWORD PTR [rbx+559904]
__sbr_cell_0_890_end:
ff_aac_sbr_apply.L7750_5:
__sbr_cell_0_891:
    sub r13, -128
__sbr_cell_0_891_end:
__sbr_cell_0_892:
    add r15, 256
__sbr_cell_0_892_end:
__sbr_cell_0_893:
    cmp r13, 4096
__sbr_cell_0_893_end:
__sbr_cell_0_894:
    jne ff_aac_sbr_apply.L7750
__sbr_cell_0_894_end:
__sbr_cell_0_895:
    mov r15, QWORD PTR [rbp-72]
__sbr_cell_0_895_end:
__sbr_cell_0_896:
    mov ecx, DWORD PTR [r15+31008]
__sbr_cell_0_896_end:
__sbr_cell_0_897:
    mov rdi, QWORD PTR [rbp-176]
__sbr_cell_0_897_end:
__sbr_cell_0_898:
    mov rsi, QWORD PTR [rbp-192]
__sbr_cell_0_898_end:
__sbr_cell_0_899:
    mov rdx, QWORD PTR [rbp-120]
__sbr_cell_0_899_end:
__sbr_cell_0_900:
    call QWORD PTR [rbx+559984]
__sbr_cell_0_900_end:
ff_aac_sbr_apply.L7750_6:
__sbr_cell_0_901:
    mov eax, DWORD PTR [r15+31008]
__sbr_cell_0_901_end:
__sbr_cell_0_902:
    xor eax, 1
__sbr_cell_0_902_end:
__sbr_cell_0_903:
    mov DWORD PTR [r15+31008], eax
__sbr_cell_0_903_end:
ff_aac_sbr_apply.L7750_7:
__sbr_cell_0_904:
    cmp DWORD PTR [rbx+166180], 0
__sbr_cell_0_904_end:
__sbr_cell_0_905:
    mov r12, r14
__sbr_cell_0_905_end:
__sbr_cell_0_906:
    mov rdi, QWORD PTR [rbp-288]
__sbr_cell_0_906_end:
__sbr_cell_0_907:
    je ff_aac_sbr_apply.L9934
__sbr_cell_0_907_end:
__sbr_cell_0_908:
    mov r8d, DWORD PTR [rbx+166240]
__sbr_cell_0_908_end:
__sbr_cell_0_909:
    mov rsi, QWORD PTR [rbp-328]
__sbr_cell_0_909_end:
__sbr_cell_0_910:
    mov rdx, QWORD PTR [rbp-320]
__sbr_cell_0_910_end:
__sbr_cell_0_911:
    mov rcx, QWORD PTR [rbp-192]
__sbr_cell_0_911_end:
__sbr_cell_0_912:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_912_end:
__sbr_cell_0_913:
    call QWORD PTR [rax+560008]
__sbr_cell_0_913_end:
ff_aac_sbr_apply.L7750_8:
__sbr_cell_0_914:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_914_end:
__sbr_cell_0_915:
    mov eax, DWORD PTR [r8+477960]
__sbr_cell_0_915_end:
__sbr_cell_0_916:
    test eax, eax
__sbr_cell_0_916_end:
__sbr_cell_0_917:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_917_end:
__sbr_cell_0_918:
    je ff_aac_sbr_apply.L7b00
__sbr_cell_0_918_end:
__sbr_cell_0_919:
    movzx ecx, BYTE PTR [rbx+39]
__sbr_cell_0_919_end:
__sbr_cell_0_920:
    movzx edx, BYTE PTR [rbx+44]
__sbr_cell_0_920_end:
__sbr_cell_0_921:
    add edx, ecx
__sbr_cell_0_921_end:
__sbr_cell_0_922:
    vmovss xmm0, DWORD PTR [rip+LCPI14_6]
__sbr_cell_0_922_end:
__sbr_cell_0_923:
    cmp edx, 1
__sbr_cell_0_923_end:
__sbr_cell_0_924:
    je ff_aac_sbr_apply.L7866
__sbr_cell_0_924_end:
__sbr_cell_0_925:
    cmp cl, 4
__sbr_cell_0_925_end:
__sbr_cell_0_926:
    jae ff_aac_sbr_apply.L9c09
__sbr_cell_0_926_end:
__sbr_cell_0_927:
    lea rdx, [rip+bw_tab]
__sbr_cell_0_927_end:
__sbr_cell_0_928:
    vmovss xmm0, DWORD PTR [rdx+rcx*4+0]
__sbr_cell_0_928_end:
ff_aac_sbr_apply.L7866:
__sbr_cell_0_929:
    vmovss xmm1, DWORD PTR [rbx+14604]
__sbr_cell_0_929_end:
__sbr_cell_0_930:
    vucomiss xmm1, xmm0
__sbr_cell_0_930_end:
__sbr_cell_0_931:
    vmovss xmm2, DWORD PTR [rip+LCPI14_9]
__sbr_cell_0_931_end:
__sbr_cell_0_932:
    ja ff_aac_sbr_apply.L7884
__sbr_cell_0_932_end:
__sbr_cell_0_933:
    vmovss xmm2, DWORD PTR [rip+LCPI14_10]
__sbr_cell_0_933_end:
ff_aac_sbr_apply.L7884:
__sbr_cell_0_934:
    vcmpltss xmm3, xmm0, xmm1
__sbr_cell_0_934_end:
__sbr_cell_0_935:
    vbroadcastss xmm4, DWORD PTR [rip+LCPI14_17]
__sbr_cell_0_935_end:
__sbr_cell_0_936:
    vblendvps xmm3, xmm4, XMMWORD PTR [rip+LCPI14_8], xmm3
__sbr_cell_0_936_end:
__sbr_cell_0_937:
    vmulss xmm0, xmm0, xmm3
__sbr_cell_0_937_end:
__sbr_cell_0_938:
    vmulss xmm1, xmm1, xmm2
__sbr_cell_0_938_end:
__sbr_cell_0_939:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_0_939_end:
__sbr_cell_0_940:
    vcmpltss xmm1, xmm0, DWORD PTR [rip+LCPI14_11]
__sbr_cell_0_940_end:
__sbr_cell_0_941:
    vandnps xmm0, xmm1, xmm0
__sbr_cell_0_941_end:
__sbr_cell_0_942:
    vmovss DWORD PTR [rbx+14604], xmm0
__sbr_cell_0_942_end:
__sbr_cell_0_943:
    cmp eax, 1
__sbr_cell_0_943_end:
__sbr_cell_0_944:
    je ff_aac_sbr_apply.L7b00
__sbr_cell_0_944_end:
ff_aac_sbr_apply.L7884_1:
__sbr_cell_0_945:
    movzx ecx, BYTE PTR [rbx+40]
__sbr_cell_0_945_end:
__sbr_cell_0_946:
    movzx edx, BYTE PTR [rbx+45]
__sbr_cell_0_946_end:
__sbr_cell_0_947:
    add edx, ecx
__sbr_cell_0_947_end:
__sbr_cell_0_948:
    vmovss xmm0, DWORD PTR [rip+LCPI14_6]
__sbr_cell_0_948_end:
__sbr_cell_0_949:
    cmp edx, 1
__sbr_cell_0_949_end:
__sbr_cell_0_950:
    je ff_aac_sbr_apply.L78f2
__sbr_cell_0_950_end:
__sbr_cell_0_951:
    cmp cl, 3
__sbr_cell_0_951_end:
__sbr_cell_0_952:
    ja ff_aac_sbr_apply.L9c09
__sbr_cell_0_952_end:
__sbr_cell_0_953:
    lea rdx, [rip+bw_tab]
__sbr_cell_0_953_end:
__sbr_cell_0_954:
    vmovss xmm0, DWORD PTR [rdx+rcx*4+0]
__sbr_cell_0_954_end:
ff_aac_sbr_apply.L78f2:
__sbr_cell_0_955:
    vmovss xmm1, DWORD PTR [rbx+14608]
__sbr_cell_0_955_end:
__sbr_cell_0_956:
    vucomiss xmm1, xmm0
__sbr_cell_0_956_end:
__sbr_cell_0_957:
    vmovss xmm2, DWORD PTR [rip+LCPI14_9]
__sbr_cell_0_957_end:
__sbr_cell_0_958:
    ja ff_aac_sbr_apply.L7910
__sbr_cell_0_958_end:
__sbr_cell_0_959:
    vmovss xmm2, DWORD PTR [rip+LCPI14_10]
__sbr_cell_0_959_end:
ff_aac_sbr_apply.L7910:
__sbr_cell_0_960:
    vcmpltss xmm3, xmm0, xmm1
__sbr_cell_0_960_end:
__sbr_cell_0_961:
    vbroadcastss xmm4, DWORD PTR [rip+LCPI14_17]
__sbr_cell_0_961_end:
__sbr_cell_0_962:
    vblendvps xmm3, xmm4, XMMWORD PTR [rip+LCPI14_8], xmm3
__sbr_cell_0_962_end:
__sbr_cell_0_963:
    vmulss xmm0, xmm0, xmm3
__sbr_cell_0_963_end:
__sbr_cell_0_964:
    vmulss xmm1, xmm1, xmm2
__sbr_cell_0_964_end:
__sbr_cell_0_965:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_0_965_end:
__sbr_cell_0_966:
    vcmpltss xmm1, xmm0, DWORD PTR [rip+LCPI14_11]
__sbr_cell_0_966_end:
__sbr_cell_0_967:
    vandnps xmm0, xmm1, xmm0
__sbr_cell_0_967_end:
__sbr_cell_0_968:
    vmovss DWORD PTR [rbx+14608], xmm0
__sbr_cell_0_968_end:
__sbr_cell_0_969:
    cmp eax, 3
__sbr_cell_0_969_end:
__sbr_cell_0_970:
    jb ff_aac_sbr_apply.L7b00
__sbr_cell_0_970_end:
ff_aac_sbr_apply.L7910_1:
__sbr_cell_0_971:
    movzx ecx, BYTE PTR [rbx+41]
__sbr_cell_0_971_end:
__sbr_cell_0_972:
    movzx edx, BYTE PTR [rbx+46]
__sbr_cell_0_972_end:
__sbr_cell_0_973:
    add edx, ecx
__sbr_cell_0_973_end:
__sbr_cell_0_974:
    vmovss xmm0, DWORD PTR [rip+LCPI14_6]
__sbr_cell_0_974_end:
__sbr_cell_0_975:
    cmp edx, 1
__sbr_cell_0_975_end:
__sbr_cell_0_976:
    je ff_aac_sbr_apply.L797e
__sbr_cell_0_976_end:
__sbr_cell_0_977:
    cmp cl, 3
__sbr_cell_0_977_end:
__sbr_cell_0_978:
    ja ff_aac_sbr_apply.L9c09
__sbr_cell_0_978_end:
__sbr_cell_0_979:
    lea rdx, [rip+bw_tab]
__sbr_cell_0_979_end:
__sbr_cell_0_980:
    vmovss xmm0, DWORD PTR [rdx+rcx*4+0]
__sbr_cell_0_980_end:
ff_aac_sbr_apply.L797e:
__sbr_cell_0_981:
    vmovss xmm1, DWORD PTR [rbx+14612]
__sbr_cell_0_981_end:
__sbr_cell_0_982:
    vucomiss xmm1, xmm0
__sbr_cell_0_982_end:
__sbr_cell_0_983:
    vmovss xmm2, DWORD PTR [rip+LCPI14_9]
__sbr_cell_0_983_end:
__sbr_cell_0_984:
    ja ff_aac_sbr_apply.L799c
__sbr_cell_0_984_end:
__sbr_cell_0_985:
    vmovss xmm2, DWORD PTR [rip+LCPI14_10]
__sbr_cell_0_985_end:
ff_aac_sbr_apply.L799c:
__sbr_cell_0_986:
    vcmpltss xmm3, xmm0, xmm1
__sbr_cell_0_986_end:
__sbr_cell_0_987:
    vbroadcastss xmm4, DWORD PTR [rip+LCPI14_17]
__sbr_cell_0_987_end:
__sbr_cell_0_988:
    vblendvps xmm3, xmm4, XMMWORD PTR [rip+LCPI14_8], xmm3
__sbr_cell_0_988_end:
__sbr_cell_0_989:
    vmulss xmm0, xmm0, xmm3
__sbr_cell_0_989_end:
__sbr_cell_0_990:
    vmulss xmm1, xmm1, xmm2
__sbr_cell_0_990_end:
__sbr_cell_0_991:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_0_991_end:
__sbr_cell_0_992:
    vcmpltss xmm1, xmm0, DWORD PTR [rip+LCPI14_11]
__sbr_cell_0_992_end:
__sbr_cell_0_993:
    vandnps xmm0, xmm1, xmm0
__sbr_cell_0_993_end:
__sbr_cell_0_994:
    vmovss DWORD PTR [rbx+14612], xmm0
__sbr_cell_0_994_end:
__sbr_cell_0_995:
    cmp eax, 3
__sbr_cell_0_995_end:
__sbr_cell_0_996:
    je ff_aac_sbr_apply.L7b00
__sbr_cell_0_996_end:
ff_aac_sbr_apply.L799c_1:
__sbr_cell_0_997:
    movzx ecx, BYTE PTR [rbx+42]
__sbr_cell_0_997_end:
__sbr_cell_0_998:
    movzx edx, BYTE PTR [rbx+47]
__sbr_cell_0_998_end:
__sbr_cell_0_999:
    add edx, ecx
__sbr_cell_0_999_end:
__sbr_cell_0_1000:
    vmovss xmm0, DWORD PTR [rip+LCPI14_6]
__sbr_cell_0_1000_end:
__sbr_cell_0_1001:
    cmp edx, 1
__sbr_cell_0_1001_end:
__sbr_cell_0_1002:
    je ff_aac_sbr_apply.L7a0a
__sbr_cell_0_1002_end:
__sbr_cell_0_1003:
    cmp cl, 3
__sbr_cell_0_1003_end:
__sbr_cell_0_1004:
    ja ff_aac_sbr_apply.L9c09
__sbr_cell_0_1004_end:
__sbr_cell_0_1005:
    lea rdx, [rip+bw_tab]
__sbr_cell_0_1005_end:
__sbr_cell_0_1006:
    vmovss xmm0, DWORD PTR [rdx+rcx*4+0]
__sbr_cell_0_1006_end:
ff_aac_sbr_apply.L7a0a:
__sbr_cell_0_1007:
    vmovss xmm1, DWORD PTR [rbx+14616]
__sbr_cell_0_1007_end:
__sbr_cell_0_1008:
    vucomiss xmm1, xmm0
__sbr_cell_0_1008_end:
__sbr_cell_0_1009:
    vmovss xmm2, DWORD PTR [rip+LCPI14_9]
__sbr_cell_0_1009_end:
__sbr_cell_0_1010:
    ja ff_aac_sbr_apply.L7a28
__sbr_cell_0_1010_end:
__sbr_cell_0_1011:
    vmovss xmm2, DWORD PTR [rip+LCPI14_10]
__sbr_cell_0_1011_end:
ff_aac_sbr_apply.L7a28:
__sbr_cell_0_1012:
    vcmpltss xmm3, xmm0, xmm1
__sbr_cell_0_1012_end:
__sbr_cell_0_1013:
    vbroadcastss xmm4, DWORD PTR [rip+LCPI14_17]
__sbr_cell_0_1013_end:
__sbr_cell_0_1014:
    vblendvps xmm3, xmm4, XMMWORD PTR [rip+LCPI14_8], xmm3
__sbr_cell_0_1014_end:
__sbr_cell_0_1015:
    vmulss xmm0, xmm0, xmm3
__sbr_cell_0_1015_end:
__sbr_cell_0_1016:
    vmulss xmm1, xmm1, xmm2
__sbr_cell_0_1016_end:
__sbr_cell_0_1017:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_0_1017_end:
__sbr_cell_0_1018:
    vcmpltss xmm1, xmm0, DWORD PTR [rip+LCPI14_11]
__sbr_cell_0_1018_end:
__sbr_cell_0_1019:
    vandnps xmm0, xmm1, xmm0
__sbr_cell_0_1019_end:
__sbr_cell_0_1020:
    vmovss DWORD PTR [rbx+14616], xmm0
__sbr_cell_0_1020_end:
__sbr_cell_0_1021:
    cmp eax, 5
__sbr_cell_0_1021_end:
__sbr_cell_0_1022:
    jb ff_aac_sbr_apply.L7b00
__sbr_cell_0_1022_end:
ff_aac_sbr_apply.L7a28_1:
__sbr_cell_0_1023:
    movzx ecx, BYTE PTR [rbx+43]
__sbr_cell_0_1023_end:
__sbr_cell_0_1024:
    movzx edx, BYTE PTR [rbx+48]
__sbr_cell_0_1024_end:
__sbr_cell_0_1025:
    add edx, ecx
__sbr_cell_0_1025_end:
__sbr_cell_0_1026:
    vmovss xmm0, DWORD PTR [rip+LCPI14_6]
__sbr_cell_0_1026_end:
__sbr_cell_0_1027:
    cmp edx, 1
__sbr_cell_0_1027_end:
__sbr_cell_0_1028:
    je ff_aac_sbr_apply.L7a96
__sbr_cell_0_1028_end:
__sbr_cell_0_1029:
    cmp cl, 3
__sbr_cell_0_1029_end:
__sbr_cell_0_1030:
    ja ff_aac_sbr_apply.L9c09
__sbr_cell_0_1030_end:
__sbr_cell_0_1031:
    lea rdx, [rip+bw_tab]
__sbr_cell_0_1031_end:
__sbr_cell_0_1032:
    vmovss xmm0, DWORD PTR [rdx+rcx*4+0]
__sbr_cell_0_1032_end:
ff_aac_sbr_apply.L7a96:
__sbr_cell_0_1033:
    vmovss xmm1, DWORD PTR [rbx+14620]
__sbr_cell_0_1033_end:
__sbr_cell_0_1034:
    vucomiss xmm1, xmm0
__sbr_cell_0_1034_end:
__sbr_cell_0_1035:
    vmovss xmm2, DWORD PTR [rip+LCPI14_9]
__sbr_cell_0_1035_end:
__sbr_cell_0_1036:
    ja ff_aac_sbr_apply.L7ab4
__sbr_cell_0_1036_end:
__sbr_cell_0_1037:
    vmovss xmm2, DWORD PTR [rip+LCPI14_10]
__sbr_cell_0_1037_end:
ff_aac_sbr_apply.L7ab4:
__sbr_cell_0_1038:
    vcmpltss xmm3, xmm0, xmm1
__sbr_cell_0_1038_end:
__sbr_cell_0_1039:
    vbroadcastss xmm4, DWORD PTR [rip+LCPI14_17]
__sbr_cell_0_1039_end:
__sbr_cell_0_1040:
    vblendvps xmm3, xmm4, XMMWORD PTR [rip+LCPI14_8], xmm3
__sbr_cell_0_1040_end:
__sbr_cell_0_1041:
    vmulss xmm0, xmm0, xmm3
__sbr_cell_0_1041_end:
__sbr_cell_0_1042:
    vmulss xmm1, xmm1, xmm2
__sbr_cell_0_1042_end:
__sbr_cell_0_1043:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_0_1043_end:
__sbr_cell_0_1044:
    vcmpltss xmm1, xmm0, DWORD PTR [rip+LCPI14_11]
__sbr_cell_0_1044_end:
__sbr_cell_0_1045:
    vandnps xmm0, xmm1, xmm0
__sbr_cell_0_1045_end:
__sbr_cell_0_1046:
    vmovss DWORD PTR [rbx+14620], xmm0
__sbr_cell_0_1046_end:
__sbr_cell_0_1047:
    cmp eax, 5
__sbr_cell_0_1047_end:
__sbr_cell_0_1048:
    jne ff_aac_sbr_apply.L9c1d
__sbr_cell_0_1048_end:
__sbr_cell_0_1049:
    .nops 1
__sbr_cell_0_1049_end:
ff_aac_sbr_apply.L7b00:
__sbr_cell_0_1050:
    movsxd rcx, DWORD PTR [rbx+8]
__sbr_cell_0_1050_end:
__sbr_cell_0_1051:
    mov QWORD PTR [rbp-48], rcx
__sbr_cell_0_1051_end:
__sbr_cell_0_1052:
    test rcx, rcx
__sbr_cell_0_1052_end:
__sbr_cell_0_1053:
    je ff_aac_sbr_apply.L9bd4
__sbr_cell_0_1053_end:
ff_aac_sbr_apply.L7b00_1:
__sbr_cell_0_1054:
    mov r12d, DWORD PTR [r8+166264]
__sbr_cell_0_1054_end:
__sbr_cell_0_1055:
    mov eax, DWORD PTR [r8+478288]
__sbr_cell_0_1055_end:
__sbr_cell_0_1056:
    test eax, eax
__sbr_cell_0_1056_end:
__sbr_cell_0_1057:
    je ff_aac_sbr_apply.L7cb0
__sbr_cell_0_1057_end:
__sbr_cell_0_1058:
    xor r13d, r13d
__sbr_cell_0_1058_end:
__sbr_cell_0_1059:
    xor r15d, r15d
__sbr_cell_0_1059_end:
ff_aac_sbr_apply.L7b2d:
__sbr_cell_0_1060:
    cmp BYTE PTR [r8+r15*1+478292], 0
__sbr_cell_0_1060_end:
__sbr_cell_0_1061:
    je ff_aac_sbr_apply.L7c5d
__sbr_cell_0_1061_end:
__sbr_cell_0_1062:
    movsxd r12, r12d
__sbr_cell_0_1062_end:
__sbr_cell_0_1063:
    xor r14d, r14d
__sbr_cell_0_1063_end:
__sbr_cell_0_1064:
    .nops 1
__sbr_cell_0_1064_end:
ff_aac_sbr_apply.L7b50:
__sbr_cell_0_1065:
    movzx eax, BYTE PTR [r8+r15*1+478298]
__sbr_cell_0_1065_end:
__sbr_cell_0_1066:
    mov ecx, DWORD PTR [r8+477960]
__sbr_cell_0_1066_end:
__sbr_cell_0_1067:
    cmp r13d, ecx
__sbr_cell_0_1067_end:
__sbr_cell_0_1068:
    ja ff_aac_sbr_apply.L7bb3
__sbr_cell_0_1068_end:
__sbr_cell_0_1069:
    mov edx, r13d
__sbr_cell_0_1069_end:
__sbr_cell_0_1070:
    lea r13d, [rcx+1]
__sbr_cell_0_1070_end:
__sbr_cell_0_1071:
    cmp rdx, 7
__sbr_cell_0_1071_end:
__sbr_cell_0_1072:
    mov esi, 6
__sbr_cell_0_1072_end:
__sbr_cell_0_1073:
    cmovae rsi, rdx
__sbr_cell_0_1073_end:
__sbr_cell_0_1074:
    inc rcx
__sbr_cell_0_1074_end:
__sbr_cell_0_1075:
    .nops 1
__sbr_cell_0_1075_end:
ff_aac_sbr_apply.L7b80:
__sbr_cell_0_1076:
    cmp rsi, rdx
__sbr_cell_0_1076_end:
__sbr_cell_0_1077:
    je ff_aac_sbr_apply.L9b4a
__sbr_cell_0_1077_end:
__sbr_cell_0_1078:
    movzx edi, WORD PTR [r8+rdx*2+478214]
__sbr_cell_0_1078_end:
__sbr_cell_0_1079:
    cmp r12, rdi
__sbr_cell_0_1079_end:
__sbr_cell_0_1080:
    jl ff_aac_sbr_apply.L7bb0
__sbr_cell_0_1080_end:
__sbr_cell_0_1081:
    inc rdx
__sbr_cell_0_1081_end:
__sbr_cell_0_1082:
    cmp rcx, rdx
__sbr_cell_0_1082_end:
__sbr_cell_0_1083:
    jne ff_aac_sbr_apply.L7b80
__sbr_cell_0_1083_end:
__sbr_cell_0_1084:
    jmp ff_aac_sbr_apply.L7bb3
__sbr_cell_0_1084_end:
__sbr_cell_0_1085:
    .nops 1
__sbr_cell_0_1085_end:
ff_aac_sbr_apply.L7bb0:
__sbr_cell_0_1086:
    mov r13d, edx
__sbr_cell_0_1086_end:
ff_aac_sbr_apply.L7bb3:
__sbr_cell_0_1087:
    test r13d, r13d
__sbr_cell_0_1087_end:
__sbr_cell_0_1088:
    jle ff_aac_sbr_apply.L7c80
__sbr_cell_0_1088_end:
__sbr_cell_0_1089:
    add eax, r14d
__sbr_cell_0_1089_end:
__sbr_cell_0_1090:
    dec r13d
__sbr_cell_0_1090_end:
__sbr_cell_0_1091:
    lea rcx, [r12+r12*4+0]
__sbr_cell_0_1091_end:
__sbr_cell_0_1092:
    shl rcx, 6
__sbr_cell_0_1092_end:
__sbr_cell_0_1093:
    mov rdx, QWORD PTR [rbp-184]
__sbr_cell_0_1093_end:
__sbr_cell_0_1094:
    lea rdi, [rdx+rcx*1+0]
__sbr_cell_0_1094_end:
__sbr_cell_0_1095:
    add rdi, 16
__sbr_cell_0_1095_end:
__sbr_cell_0_1096:
    mov eax, eax
__sbr_cell_0_1096_end:
__sbr_cell_0_1097:
    lea rcx, [rax+rax*4+0]
__sbr_cell_0_1097_end:
__sbr_cell_0_1098:
    shl rcx, 6
__sbr_cell_0_1098_end:
__sbr_cell_0_1099:
    mov rdx, QWORD PTR [rbp-192]
__sbr_cell_0_1099_end:
__sbr_cell_0_1100:
    lea rsi, [rdx+rcx*1+0]
__sbr_cell_0_1100_end:
__sbr_cell_0_1101:
    add rsi, 16
__sbr_cell_0_1101_end:
ff_aac_sbr_apply.L7bb3_1:
__sbr_cell_0_1102:
    mov rcx, QWORD PTR [rbp-328]
__sbr_cell_0_1102_end:
__sbr_cell_0_1103:
    lea rdx, [rcx+rax*8+0]
__sbr_cell_0_1103_end:
__sbr_cell_0_1104:
    mov rcx, QWORD PTR [rbp-320]
__sbr_cell_0_1104_end:
__sbr_cell_0_1105:
    lea rcx, [rcx+rax*8+0]
__sbr_cell_0_1105_end:
__sbr_cell_0_1106:
    vmovss xmm0, DWORD PTR [rbx+r13*4+14604]
__sbr_cell_0_1106_end:
__sbr_cell_0_1107:
    movzx r8d, BYTE PTR [rbx+88732]
__sbr_cell_0_1107_end:
__sbr_cell_0_1108:
    add r8d, r8d
__sbr_cell_0_1108_end:
__sbr_cell_0_1109:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_0_1109_end:
__sbr_cell_0_1110:
    movzx r9d, BYTE PTR [rbx+rax*1+88732]
__sbr_cell_0_1110_end:
__sbr_cell_0_1111:
    add r9d, r9d
__sbr_cell_0_1111_end:
__sbr_cell_0_1112:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_0_1112_end:
__sbr_cell_0_1113:
    call QWORD PTR [rbx+559936]
__sbr_cell_0_1113_end:
ff_aac_sbr_apply.L7bb3_2:
__sbr_cell_0_1114:
    mov r8, rbx
__sbr_cell_0_1114_end:
__sbr_cell_0_1115:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_1115_end:
__sbr_cell_0_1116:
    inc r14d
__sbr_cell_0_1116_end:
__sbr_cell_0_1117:
    inc r12
__sbr_cell_0_1117_end:
__sbr_cell_0_1118:
    movzx eax, BYTE PTR [r8+r15*1+478292]
__sbr_cell_0_1118_end:
__sbr_cell_0_1119:
    cmp r14d, eax
__sbr_cell_0_1119_end:
__sbr_cell_0_1120:
    jb ff_aac_sbr_apply.L7b50
__sbr_cell_0_1120_end:
__sbr_cell_0_1121:
    mov eax, DWORD PTR [r8+478288]
__sbr_cell_0_1121_end:
ff_aac_sbr_apply.L7c5d:
__sbr_cell_0_1122:
    inc r15
__sbr_cell_0_1122_end:
__sbr_cell_0_1123:
    mov ecx, eax
__sbr_cell_0_1123_end:
__sbr_cell_0_1124:
    cmp r15, rcx
__sbr_cell_0_1124_end:
__sbr_cell_0_1125:
    jae ff_aac_sbr_apply.L8b4f
__sbr_cell_0_1125_end:
__sbr_cell_0_1126:
    cmp r15, 6
__sbr_cell_0_1126_end:
__sbr_cell_0_1127:
    jne ff_aac_sbr_apply.L7b2d
__sbr_cell_0_1127_end:
__sbr_cell_0_1128:
    jmp ff_aac_sbr_apply.L9a5f
__sbr_cell_0_1128_end:
__sbr_cell_0_1129:
    .nops 1
__sbr_cell_0_1129_end:
ff_aac_sbr_apply.L7c80:
__sbr_cell_0_1130:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_0_1130_end:
__sbr_cell_0_1131:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_0_1131_end:
__sbr_cell_0_1132:
    mov esi, 16
__sbr_cell_0_1132_end:
__sbr_cell_0_1133:
    lea rdx, [rip+L_str_35]
__sbr_cell_0_1133_end:
__sbr_cell_0_1134:
    mov ecx, r12d
__sbr_cell_0_1134_end:
__sbr_cell_0_1135:
    xor eax, eax
__sbr_cell_0_1135_end:
__sbr_cell_0_1136:
    call av_log
__sbr_cell_0_1136_end:
ff_aac_sbr_apply.L7c80_1:
__sbr_cell_0_1137:
    jmp ff_aac_sbr_apply.L7ce0
__sbr_cell_0_1137_end:
__sbr_cell_0_1138:
    .nops 1
__sbr_cell_0_1138_end:
ff_aac_sbr_apply.L7cb0:
__sbr_cell_0_1139:
    mov eax, r12d
__sbr_cell_0_1139_end:
__sbr_cell_0_1140:
    add eax, DWORD PTR [r8+166272]
__sbr_cell_0_1140_end:
__sbr_cell_0_1141:
    sub eax, r12d
__sbr_cell_0_1141_end:
__sbr_cell_0_1142:
    jbe ff_aac_sbr_apply.L7ce4
__sbr_cell_0_1142_end:
ff_aac_sbr_apply.L7cbf:
__sbr_cell_0_1143:
    movsxd rcx, r12d
__sbr_cell_0_1143_end:
__sbr_cell_0_1144:
    lea rdi, [rcx+rcx*4+0]
__sbr_cell_0_1144_end:
__sbr_cell_0_1145:
    shl rdi, 6
__sbr_cell_0_1145_end:
__sbr_cell_0_1146:
    add rdi, QWORD PTR [rbp-184]
__sbr_cell_0_1146_end:
__sbr_cell_0_1147:
    shl rax, 6
__sbr_cell_0_1147_end:
__sbr_cell_0_1148:
    lea rdx, [rax+rax*4+0]
__sbr_cell_0_1148_end:
__sbr_cell_0_1149:
    xor esi, esi
__sbr_cell_0_1149_end:
__sbr_cell_0_1150:
    call memset
__sbr_cell_0_1150_end:
ff_aac_sbr_apply.L7ce0:
__sbr_cell_0_1151:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1151_end:
ff_aac_sbr_apply.L7ce4:
__sbr_cell_0_1152:
    lea r10, [rbx+86064]
__sbr_cell_0_1152_end:
__sbr_cell_0_1153:
    vxorps xmm0, xmm0, xmm0
__sbr_cell_0_1153_end:
__sbr_cell_0_1154:
    vmovups YMMWORD PTR [rbx+86416], ymm0
__sbr_cell_0_1154_end:
__sbr_cell_0_1155:
    vmovaps YMMWORD PTR [rbx+86400], ymm0
__sbr_cell_0_1155_end:
__sbr_cell_0_1156:
    vmovaps YMMWORD PTR [rbx+86368], ymm0
__sbr_cell_0_1156_end:
__sbr_cell_0_1157:
    vmovaps YMMWORD PTR [rbx+86336], ymm0
__sbr_cell_0_1157_end:
__sbr_cell_0_1158:
    vmovaps YMMWORD PTR [rbx+86304], ymm0
__sbr_cell_0_1158_end:
__sbr_cell_0_1159:
    vmovaps YMMWORD PTR [rbx+86272], ymm0
__sbr_cell_0_1159_end:
__sbr_cell_0_1160:
    vmovaps YMMWORD PTR [rbx+86240], ymm0
__sbr_cell_0_1160_end:
__sbr_cell_0_1161:
    vmovaps YMMWORD PTR [rbx+86208], ymm0
__sbr_cell_0_1161_end:
ff_aac_sbr_apply.L7ce4_1:
__sbr_cell_0_1162:
    vmovaps YMMWORD PTR [rbx+86176], ymm0
__sbr_cell_0_1162_end:
__sbr_cell_0_1163:
    vmovaps YMMWORD PTR [rbx+86144], ymm0
__sbr_cell_0_1163_end:
__sbr_cell_0_1164:
    vmovaps YMMWORD PTR [rbx+86112], ymm0
__sbr_cell_0_1164_end:
ff_aac_sbr_apply.L7ce4_2:
__sbr_cell_0_1165:
    cmp DWORD PTR [rbx+8], 0
__sbr_cell_0_1165_end:
__sbr_cell_0_1166:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_1166_end:
__sbr_cell_0_1167:
    je ff_aac_sbr_apply.L8790
__sbr_cell_0_1167_end:
__sbr_cell_0_1168:
    lea rax, [rbx+86928]
__sbr_cell_0_1168_end:
__sbr_cell_0_1169:
    mov QWORD PTR [rbp-224], rax
__sbr_cell_0_1169_end:
__sbr_cell_0_1170:
    lea rax, [rbx+88672]
__sbr_cell_0_1170_end:
__sbr_cell_0_1171:
    mov QWORD PTR [rbp-216], rax
__sbr_cell_0_1171_end:
ff_aac_sbr_apply.L7ce4_3:
__sbr_cell_0_1172:
    mov rax, QWORD PTR [rbp-384]
__sbr_cell_0_1172_end:
__sbr_cell_0_1173:
    mov rcx, QWORD PTR [rbp-152]
__sbr_cell_0_1173_end:
__sbr_cell_0_1174:
    lea r11, [rax+rcx*1+0]
__sbr_cell_0_1174_end:
__sbr_cell_0_1175:
    mov ecx, 1
__sbr_cell_0_1175_end:
__sbr_cell_0_1176:
    mov QWORD PTR [rbp-96], r8
__sbr_cell_0_1176_end:
ff_aac_sbr_apply.L7ce4_4:
__sbr_cell_0_1177:
    mov rax, QWORD PTR [rbp-392]
__sbr_cell_0_1177_end:
__sbr_cell_0_1178:
    mov QWORD PTR [rbp-88], rax
__sbr_cell_0_1178_end:
ff_aac_sbr_apply.L7ce4_5:
__sbr_cell_0_1179:
    mov r12, QWORD PTR [rbp-208]
__sbr_cell_0_1179_end:
__sbr_cell_0_1180:
    xor eax, eax
__sbr_cell_0_1180_end:
__sbr_cell_0_1181:
    mov QWORD PTR [rbp-128], r10
__sbr_cell_0_1181_end:
__sbr_cell_0_1182:
    mov QWORD PTR [rbp-232], r11
__sbr_cell_0_1182_end:
__sbr_cell_0_1183:
    .nops 1
__sbr_cell_0_1183_end:
ff_aac_sbr_apply.L7db0:
__sbr_cell_0_1184:
    mov r14, rcx
__sbr_cell_0_1184_end:
__sbr_cell_0_1185:
    movzx ecx, BYTE PTR [rbx+rcx*1+12]
__sbr_cell_0_1185_end:
__sbr_cell_0_1186:
    cmp rcx, 2
__sbr_cell_0_1186_end:
__sbr_cell_0_1187:
    jae ff_aac_sbr_apply.L9b77
__sbr_cell_0_1187_end:
__sbr_cell_0_1188:
    test rcx, rcx
__sbr_cell_0_1188_end:
__sbr_cell_0_1189:
    mov r15, QWORD PTR [rbp-440]
__sbr_cell_0_1189_end:
__sbr_cell_0_1190:
    cmove r15, QWORD PTR [rbp-432]
__sbr_cell_0_1190_end:
__sbr_cell_0_1191:
    mov edx, DWORD PTR [r8+166264]
__sbr_cell_0_1191_end:
__sbr_cell_0_1192:
    movzx edi, WORD PTR [r15+0]
__sbr_cell_0_1192_end:
__sbr_cell_0_1193:
    mov DWORD PTR [rbp-48], edx
__sbr_cell_0_1193_end:
__sbr_cell_0_1194:
    cmp edx, edi
__sbr_cell_0_1194_end:
__sbr_cell_0_1195:
    jne ff_aac_sbr_apply.L879e
__sbr_cell_0_1195_end:
ff_aac_sbr_apply.L7db0_1:
__sbr_cell_0_1196:
    mov ecx, DWORD PTR [r8+rcx*4+477952]
__sbr_cell_0_1196_end:
__sbr_cell_0_1197:
    mov QWORD PTR [rbp-80], rcx
__sbr_cell_0_1197_end:
__sbr_cell_0_1198:
    test rcx, rcx
__sbr_cell_0_1198_end:
__sbr_cell_0_1199:
    je ff_aac_sbr_apply.L7e90
__sbr_cell_0_1199_end:
__sbr_cell_0_1200:
    lea rcx, [r14+r14*2+0]
__sbr_cell_0_1200_end:
__sbr_cell_0_1201:
    shl rcx, 6
__sbr_cell_0_1201_end:
__sbr_cell_0_1202:
    add rcx, QWORD PTR [rbp-224]
__sbr_cell_0_1202_end:
__sbr_cell_0_1203:
    xor edx, edx
__sbr_cell_0_1203_end:
__sbr_cell_0_1204:
    jmp ff_aac_sbr_apply.L7e29
__sbr_cell_0_1204_end:
__sbr_cell_0_1205:
    .nops 1
__sbr_cell_0_1205_end:
ff_aac_sbr_apply.L7e20:
__sbr_cell_0_1206:
    mov edi, r9d
__sbr_cell_0_1206_end:
__sbr_cell_0_1207:
    cmp rdx, QWORD PTR [rbp-80]
__sbr_cell_0_1207_end:
__sbr_cell_0_1208:
    je ff_aac_sbr_apply.L7e90
__sbr_cell_0_1208_end:
ff_aac_sbr_apply.L7e29:
__sbr_cell_0_1209:
    mov rsi, rdx
__sbr_cell_0_1209_end:
__sbr_cell_0_1210:
    inc rdx
__sbr_cell_0_1210_end:
__sbr_cell_0_1211:
    movzx r9d, WORD PTR [r15+rsi*2+2]
__sbr_cell_0_1211_end:
__sbr_cell_0_1212:
    cmp di, r9w
__sbr_cell_0_1212_end:
__sbr_cell_0_1213:
    jae ff_aac_sbr_apply.L7e20
__sbr_cell_0_1213_end:
__sbr_cell_0_1214:
    cmp rsi, 47
__sbr_cell_0_1214_end:
__sbr_cell_0_1215:
    ja ff_aac_sbr_apply.L9b5e
__sbr_cell_0_1215_end:
__sbr_cell_0_1216:
    movzx edi, di
__sbr_cell_0_1216_end:
__sbr_cell_0_1217:
    mov r8d, edi
__sbr_cell_0_1217_end:
__sbr_cell_0_1218:
    sub r8d, DWORD PTR [rbp-48]
__sbr_cell_0_1218_end:
__sbr_cell_0_1219:
    cmp r8d, 47
__sbr_cell_0_1219_end:
__sbr_cell_0_1220:
    ja ff_aac_sbr_apply.L99e9
__sbr_cell_0_1220_end:
__sbr_cell_0_1221:
    mov r8d, r8d
__sbr_cell_0_1221_end:
__sbr_cell_0_1222:
    inc rdi
__sbr_cell_0_1222_end:
__sbr_cell_0_1223:
    .nops 1
__sbr_cell_0_1223_end:
ff_aac_sbr_apply.L7e60:
__sbr_cell_0_1224:
    vmovss xmm0, DWORD PTR [rcx+rsi*4+0]
__sbr_cell_0_1224_end:
__sbr_cell_0_1225:
    vmovss DWORD PTR [r12+r8*4+0], xmm0
__sbr_cell_0_1225_end:
ff_aac_sbr_apply.L7e60_1:
__sbr_cell_0_1226:
    movzx r9d, WORD PTR [r15+rdx*2+0]
__sbr_cell_0_1226_end:
__sbr_cell_0_1227:
    cmp rdi, r9
__sbr_cell_0_1227_end:
__sbr_cell_0_1228:
    jae ff_aac_sbr_apply.L7e20
__sbr_cell_0_1228_end:
__sbr_cell_0_1229:
    inc r8
__sbr_cell_0_1229_end:
__sbr_cell_0_1230:
    inc rdi
__sbr_cell_0_1230_end:
__sbr_cell_0_1231:
    cmp r8d, 48
__sbr_cell_0_1231_end:
__sbr_cell_0_1232:
    jb ff_aac_sbr_apply.L7e60
__sbr_cell_0_1232_end:
__sbr_cell_0_1233:
    jmp ff_aac_sbr_apply.L99e9
__sbr_cell_0_1233_end:
__sbr_cell_0_1234:
    .nops 1
__sbr_cell_0_1234_end:
ff_aac_sbr_apply.L7e90:
__sbr_cell_0_1235:
    mov QWORD PTR [rbp-104], r14
__sbr_cell_0_1235_end:
__sbr_cell_0_1236:
    mov edx, 1
__sbr_cell_0_1236_end:
ff_aac_sbr_apply.L7e90_1:
__sbr_cell_0_1237:
    cmp DWORD PTR [rbx+24], 2
__sbr_cell_0_1237_end:
__sbr_cell_0_1238:
    jb ff_aac_sbr_apply.L7eb6
__sbr_cell_0_1238_end:
__sbr_cell_0_1239:
    movzx ecx, BYTE PTR [rbx+rax*1+88732]
__sbr_cell_0_1239_end:
__sbr_cell_0_1240:
    cmp cl, BYTE PTR [rbx+88743]
__sbr_cell_0_1240_end:
__sbr_cell_0_1241:
    mov edx, 2
__sbr_cell_0_1241_end:
__sbr_cell_0_1242:
    sbb rdx, 0
__sbr_cell_0_1242_end:
ff_aac_sbr_apply.L7eb6:
__sbr_cell_0_1243:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1243_end:
__sbr_cell_0_1244:
    mov ecx, DWORD PTR [r8+477960]
__sbr_cell_0_1244_end:
__sbr_cell_0_1245:
    test ecx, ecx
__sbr_cell_0_1245_end:
__sbr_cell_0_1246:
    je ff_aac_sbr_apply.L8520
__sbr_cell_0_1246_end:
__sbr_cell_0_1247:
    lea rdx, [rdx+rdx*4+0]
__sbr_cell_0_1247_end:
__sbr_cell_0_1248:
    mov rsi, QWORD PTR [rbp-216]
__sbr_cell_0_1248_end:
__sbr_cell_0_1249:
    lea rdx, [rsi+rdx*4+0]
__sbr_cell_0_1249_end:
__sbr_cell_0_1250:
    movzx edi, WORD PTR [r8+478214]
__sbr_cell_0_1250_end:
__sbr_cell_0_1251:
    movzx esi, WORD PTR [r8+478216]
__sbr_cell_0_1251_end:
__sbr_cell_0_1252:
    cmp di, si
__sbr_cell_0_1252_end:
__sbr_cell_0_1253:
    jae ff_aac_sbr_apply.L8009
__sbr_cell_0_1253_end:
__sbr_cell_0_1254:
    mov r8, rsi
__sbr_cell_0_1254_end:
__sbr_cell_0_1255:
    sub r8, rdi
__sbr_cell_0_1255_end:
__sbr_cell_0_1256:
    mov r9, r8
__sbr_cell_0_1256_end:
__sbr_cell_0_1257:
    and r9, 3
__sbr_cell_0_1257_end:
ff_aac_sbr_apply.L7eb6_1:
__sbr_cell_0_1258:
    je ff_aac_sbr_apply.L7f36
__sbr_cell_0_1258_end:
__sbr_cell_0_1259:
    mov r10d, edi
__sbr_cell_0_1259_end:
__sbr_cell_0_1260:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1260_end:
__sbr_cell_0_1261:
    neg r9
__sbr_cell_0_1261_end:
__sbr_cell_0_1262:
    xor r11d, r11d
__sbr_cell_0_1262_end:
__sbr_cell_0_1263:
    .nops 1
__sbr_cell_0_1263_end:
ff_aac_sbr_apply.L7f10:
__sbr_cell_0_1264:
    cmp r10d, 47
__sbr_cell_0_1264_end:
__sbr_cell_0_1265:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1265_end:
__sbr_cell_0_1266:
    vmovss xmm0, DWORD PTR [rdx+0]
__sbr_cell_0_1266_end:
__sbr_cell_0_1267:
    mov rbx, QWORD PTR [rbp-88]
__sbr_cell_0_1267_end:
__sbr_cell_0_1268:
    vmovss DWORD PTR [rbx+r10*4+0], xmm0
__sbr_cell_0_1268_end:
__sbr_cell_0_1269:
    dec r11
__sbr_cell_0_1269_end:
__sbr_cell_0_1270:
    inc r10
__sbr_cell_0_1270_end:
__sbr_cell_0_1271:
    cmp r9, r11
__sbr_cell_0_1271_end:
__sbr_cell_0_1272:
    jne ff_aac_sbr_apply.L7f10
__sbr_cell_0_1272_end:
__sbr_cell_0_1273:
    sub rdi, r11
__sbr_cell_0_1273_end:
ff_aac_sbr_apply.L7f36:
__sbr_cell_0_1274:
    dec r8
__sbr_cell_0_1274_end:
__sbr_cell_0_1275:
    cmp r8, 3
__sbr_cell_0_1275_end:
__sbr_cell_0_1276:
    jb ff_aac_sbr_apply.L8009
__sbr_cell_0_1276_end:
__sbr_cell_0_1277:
    mov r8d, edi
__sbr_cell_0_1277_end:
__sbr_cell_0_1278:
    sub r8d, DWORD PTR [rbp-48]
__sbr_cell_0_1278_end:
__sbr_cell_0_1279:
    lea r9d, [r8+3]
__sbr_cell_0_1279_end:
__sbr_cell_0_1280:
    mov rbx, QWORD PTR [rbp-96]
__sbr_cell_0_1280_end:
__sbr_cell_0_1281:
    lea r9, [rbx+r9*4+0]
__sbr_cell_0_1281_end:
__sbr_cell_0_1282:
    lea r10d, [r8+2]
__sbr_cell_0_1282_end:
__sbr_cell_0_1283:
    lea r10, [rbx+r10*4+0]
__sbr_cell_0_1283_end:
__sbr_cell_0_1284:
    mov r11d, r8d
__sbr_cell_0_1284_end:
__sbr_cell_0_1285:
    inc r11d
__sbr_cell_0_1285_end:
__sbr_cell_0_1286:
    lea r11, [rbx+r11*4+0]
__sbr_cell_0_1286_end:
__sbr_cell_0_1287:
    sub rdi, rsi
__sbr_cell_0_1287_end:
__sbr_cell_0_1288:
    lea rbx, [rbx+r8*4+0]
__sbr_cell_0_1288_end:
ff_aac_sbr_apply.L7f36_1:
__sbr_cell_0_1289:
    mov r14d, 137624
__sbr_cell_0_1289_end:
__sbr_cell_0_1290:
    .nops 1
__sbr_cell_0_1290_end:
ff_aac_sbr_apply.L7f80:
__sbr_cell_0_1291:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1291_end:
__sbr_cell_0_1292:
    add r13d, 4294829672
__sbr_cell_0_1292_end:
__sbr_cell_0_1293:
    cmp r13d, 48
__sbr_cell_0_1293_end:
__sbr_cell_0_1294:
    jae ff_aac_sbr_apply.L9b40
__sbr_cell_0_1294_end:
__sbr_cell_0_1295:
    vmovss xmm0, DWORD PTR [rdx+0]
__sbr_cell_0_1295_end:
__sbr_cell_0_1296:
    vmovss DWORD PTR [rbx+r14*4+0], xmm0
__sbr_cell_0_1296_end:
__sbr_cell_0_1297:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1297_end:
__sbr_cell_0_1298:
    add r13d, 4294829673
__sbr_cell_0_1298_end:
__sbr_cell_0_1299:
    cmp r13d, 47
__sbr_cell_0_1299_end:
__sbr_cell_0_1300:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1300_end:
__sbr_cell_0_1301:
    vmovss DWORD PTR [r11+r14*4+0], xmm0
__sbr_cell_0_1301_end:
__sbr_cell_0_1302:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1302_end:
__sbr_cell_0_1303:
    add r13d, 4294829674
__sbr_cell_0_1303_end:
__sbr_cell_0_1304:
    cmp r13d, 47
__sbr_cell_0_1304_end:
__sbr_cell_0_1305:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1305_end:
ff_aac_sbr_apply.L7f80_1:
__sbr_cell_0_1306:
    vmovss DWORD PTR [r10+r14*4+0], xmm0
__sbr_cell_0_1306_end:
__sbr_cell_0_1307:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1307_end:
__sbr_cell_0_1308:
    add r13d, 4294829675
__sbr_cell_0_1308_end:
__sbr_cell_0_1309:
    cmp r13d, 47
__sbr_cell_0_1309_end:
__sbr_cell_0_1310:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1310_end:
__sbr_cell_0_1311:
    vmovss DWORD PTR [r9+r14*4+0], xmm0
__sbr_cell_0_1311_end:
__sbr_cell_0_1312:
    lea r13, [rdi+r14*1+0]
__sbr_cell_0_1312_end:
__sbr_cell_0_1313:
    add r13, 4
__sbr_cell_0_1313_end:
__sbr_cell_0_1314:
    add r14, 4
__sbr_cell_0_1314_end:
__sbr_cell_0_1315:
    cmp r13, 137624
__sbr_cell_0_1315_end:
__sbr_cell_0_1316:
    jne ff_aac_sbr_apply.L7f80
__sbr_cell_0_1316_end:
ff_aac_sbr_apply.L8009:
__sbr_cell_0_1317:
    cmp ecx, 1
__sbr_cell_0_1317_end:
__sbr_cell_0_1318:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1318_end:
__sbr_cell_0_1319:
    je ff_aac_sbr_apply.L8520
__sbr_cell_0_1319_end:
__sbr_cell_0_1320:
    movzx edi, WORD PTR [r8+478218]
__sbr_cell_0_1320_end:
__sbr_cell_0_1321:
    cmp si, di
__sbr_cell_0_1321_end:
__sbr_cell_0_1322:
    jae ff_aac_sbr_apply.L814a
__sbr_cell_0_1322_end:
__sbr_cell_0_1323:
    mov r8, rdi
__sbr_cell_0_1323_end:
__sbr_cell_0_1324:
    sub r8, rsi
__sbr_cell_0_1324_end:
__sbr_cell_0_1325:
    mov r9, r8
__sbr_cell_0_1325_end:
__sbr_cell_0_1326:
    and r9, 3
__sbr_cell_0_1326_end:
__sbr_cell_0_1327:
    je ff_aac_sbr_apply.L8077
__sbr_cell_0_1327_end:
__sbr_cell_0_1328:
    mov r10d, esi
__sbr_cell_0_1328_end:
__sbr_cell_0_1329:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1329_end:
__sbr_cell_0_1330:
    neg r9
__sbr_cell_0_1330_end:
__sbr_cell_0_1331:
    xor r11d, r11d
__sbr_cell_0_1331_end:
__sbr_cell_0_1332:
    .nops 1
__sbr_cell_0_1332_end:
ff_aac_sbr_apply.L8050:
__sbr_cell_0_1333:
    cmp r10d, 47
__sbr_cell_0_1333_end:
__sbr_cell_0_1334:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1334_end:
__sbr_cell_0_1335:
    vmovss xmm0, DWORD PTR [rdx+4]
__sbr_cell_0_1335_end:
__sbr_cell_0_1336:
    mov rbx, QWORD PTR [rbp-88]
__sbr_cell_0_1336_end:
__sbr_cell_0_1337:
    vmovss DWORD PTR [rbx+r10*4+0], xmm0
__sbr_cell_0_1337_end:
__sbr_cell_0_1338:
    dec r11
__sbr_cell_0_1338_end:
__sbr_cell_0_1339:
    inc r10
__sbr_cell_0_1339_end:
__sbr_cell_0_1340:
    cmp r9, r11
__sbr_cell_0_1340_end:
__sbr_cell_0_1341:
    jne ff_aac_sbr_apply.L8050
__sbr_cell_0_1341_end:
__sbr_cell_0_1342:
    sub rsi, r11
__sbr_cell_0_1342_end:
ff_aac_sbr_apply.L8077:
__sbr_cell_0_1343:
    dec r8
__sbr_cell_0_1343_end:
__sbr_cell_0_1344:
    cmp r8, 3
__sbr_cell_0_1344_end:
__sbr_cell_0_1345:
    jb ff_aac_sbr_apply.L814a
__sbr_cell_0_1345_end:
__sbr_cell_0_1346:
    mov r8d, esi
__sbr_cell_0_1346_end:
__sbr_cell_0_1347:
    sub r8d, DWORD PTR [rbp-48]
__sbr_cell_0_1347_end:
__sbr_cell_0_1348:
    lea r9d, [r8+3]
__sbr_cell_0_1348_end:
__sbr_cell_0_1349:
    mov rbx, QWORD PTR [rbp-96]
__sbr_cell_0_1349_end:
__sbr_cell_0_1350:
    lea r9, [rbx+r9*4+0]
__sbr_cell_0_1350_end:
__sbr_cell_0_1351:
    lea r10d, [r8+2]
__sbr_cell_0_1351_end:
__sbr_cell_0_1352:
    lea r10, [rbx+r10*4+0]
__sbr_cell_0_1352_end:
__sbr_cell_0_1353:
    mov r11d, r8d
__sbr_cell_0_1353_end:
__sbr_cell_0_1354:
    inc r11d
__sbr_cell_0_1354_end:
__sbr_cell_0_1355:
    lea r11, [rbx+r11*4+0]
__sbr_cell_0_1355_end:
__sbr_cell_0_1356:
    sub rsi, rdi
__sbr_cell_0_1356_end:
__sbr_cell_0_1357:
    lea rbx, [rbx+r8*4+0]
__sbr_cell_0_1357_end:
ff_aac_sbr_apply.L8077_1:
__sbr_cell_0_1358:
    mov r14d, 137624
__sbr_cell_0_1358_end:
__sbr_cell_0_1359:
    .nops 1
__sbr_cell_0_1359_end:
ff_aac_sbr_apply.L80c0:
__sbr_cell_0_1360:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1360_end:
__sbr_cell_0_1361:
    add r13d, 4294829672
__sbr_cell_0_1361_end:
__sbr_cell_0_1362:
    cmp r13d, 47
__sbr_cell_0_1362_end:
__sbr_cell_0_1363:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1363_end:
__sbr_cell_0_1364:
    vmovss xmm0, DWORD PTR [rdx+4]
__sbr_cell_0_1364_end:
__sbr_cell_0_1365:
    vmovss DWORD PTR [rbx+r14*4+0], xmm0
__sbr_cell_0_1365_end:
__sbr_cell_0_1366:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1366_end:
__sbr_cell_0_1367:
    add r13d, 4294829673
__sbr_cell_0_1367_end:
__sbr_cell_0_1368:
    cmp r13d, 47
__sbr_cell_0_1368_end:
__sbr_cell_0_1369:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1369_end:
__sbr_cell_0_1370:
    vmovss DWORD PTR [r11+r14*4+0], xmm0
__sbr_cell_0_1370_end:
__sbr_cell_0_1371:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1371_end:
__sbr_cell_0_1372:
    add r13d, 4294829674
__sbr_cell_0_1372_end:
__sbr_cell_0_1373:
    cmp r13d, 47
__sbr_cell_0_1373_end:
__sbr_cell_0_1374:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1374_end:
ff_aac_sbr_apply.L80c0_1:
__sbr_cell_0_1375:
    vmovss DWORD PTR [r10+r14*4+0], xmm0
__sbr_cell_0_1375_end:
__sbr_cell_0_1376:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1376_end:
__sbr_cell_0_1377:
    add r13d, 4294829675
__sbr_cell_0_1377_end:
__sbr_cell_0_1378:
    cmp r13d, 47
__sbr_cell_0_1378_end:
__sbr_cell_0_1379:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1379_end:
__sbr_cell_0_1380:
    vmovss DWORD PTR [r9+r14*4+0], xmm0
__sbr_cell_0_1380_end:
__sbr_cell_0_1381:
    lea r13, [rsi+r14*1+0]
__sbr_cell_0_1381_end:
__sbr_cell_0_1382:
    add r13, 4
__sbr_cell_0_1382_end:
__sbr_cell_0_1383:
    add r14, 4
__sbr_cell_0_1383_end:
__sbr_cell_0_1384:
    cmp r13, 137624
__sbr_cell_0_1384_end:
__sbr_cell_0_1385:
    jne ff_aac_sbr_apply.L80c0
__sbr_cell_0_1385_end:
ff_aac_sbr_apply.L814a:
__sbr_cell_0_1386:
    cmp ecx, 2
__sbr_cell_0_1386_end:
__sbr_cell_0_1387:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1387_end:
__sbr_cell_0_1388:
    je ff_aac_sbr_apply.L8520
__sbr_cell_0_1388_end:
__sbr_cell_0_1389:
    movzx esi, WORD PTR [r8+478220]
__sbr_cell_0_1389_end:
__sbr_cell_0_1390:
    cmp di, si
__sbr_cell_0_1390_end:
__sbr_cell_0_1391:
    jae ff_aac_sbr_apply.L828a
__sbr_cell_0_1391_end:
__sbr_cell_0_1392:
    mov r8, rsi
__sbr_cell_0_1392_end:
__sbr_cell_0_1393:
    sub r8, rdi
__sbr_cell_0_1393_end:
__sbr_cell_0_1394:
    mov r9, r8
__sbr_cell_0_1394_end:
__sbr_cell_0_1395:
    and r9, 3
__sbr_cell_0_1395_end:
__sbr_cell_0_1396:
    je ff_aac_sbr_apply.L81b7
__sbr_cell_0_1396_end:
__sbr_cell_0_1397:
    mov r10d, edi
__sbr_cell_0_1397_end:
__sbr_cell_0_1398:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1398_end:
__sbr_cell_0_1399:
    neg r9
__sbr_cell_0_1399_end:
__sbr_cell_0_1400:
    xor r11d, r11d
__sbr_cell_0_1400_end:
__sbr_cell_0_1401:
    .nops 1
__sbr_cell_0_1401_end:
ff_aac_sbr_apply.L8190:
__sbr_cell_0_1402:
    cmp r10d, 47
__sbr_cell_0_1402_end:
__sbr_cell_0_1403:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1403_end:
__sbr_cell_0_1404:
    vmovss xmm0, DWORD PTR [rdx+8]
__sbr_cell_0_1404_end:
__sbr_cell_0_1405:
    mov rbx, QWORD PTR [rbp-88]
__sbr_cell_0_1405_end:
__sbr_cell_0_1406:
    vmovss DWORD PTR [rbx+r10*4+0], xmm0
__sbr_cell_0_1406_end:
__sbr_cell_0_1407:
    dec r11
__sbr_cell_0_1407_end:
__sbr_cell_0_1408:
    inc r10
__sbr_cell_0_1408_end:
__sbr_cell_0_1409:
    cmp r9, r11
__sbr_cell_0_1409_end:
__sbr_cell_0_1410:
    jne ff_aac_sbr_apply.L8190
__sbr_cell_0_1410_end:
__sbr_cell_0_1411:
    sub rdi, r11
__sbr_cell_0_1411_end:
ff_aac_sbr_apply.L81b7:
__sbr_cell_0_1412:
    dec r8
__sbr_cell_0_1412_end:
__sbr_cell_0_1413:
    cmp r8, 3
__sbr_cell_0_1413_end:
__sbr_cell_0_1414:
    jb ff_aac_sbr_apply.L828a
__sbr_cell_0_1414_end:
__sbr_cell_0_1415:
    mov r8d, edi
__sbr_cell_0_1415_end:
__sbr_cell_0_1416:
    sub r8d, DWORD PTR [rbp-48]
__sbr_cell_0_1416_end:
__sbr_cell_0_1417:
    lea r9d, [r8+3]
__sbr_cell_0_1417_end:
__sbr_cell_0_1418:
    mov rbx, QWORD PTR [rbp-96]
__sbr_cell_0_1418_end:
__sbr_cell_0_1419:
    lea r9, [rbx+r9*4+0]
__sbr_cell_0_1419_end:
__sbr_cell_0_1420:
    lea r10d, [r8+2]
__sbr_cell_0_1420_end:
__sbr_cell_0_1421:
    lea r10, [rbx+r10*4+0]
__sbr_cell_0_1421_end:
__sbr_cell_0_1422:
    mov r11d, r8d
__sbr_cell_0_1422_end:
__sbr_cell_0_1423:
    inc r11d
__sbr_cell_0_1423_end:
__sbr_cell_0_1424:
    lea r11, [rbx+r11*4+0]
__sbr_cell_0_1424_end:
__sbr_cell_0_1425:
    sub rdi, rsi
__sbr_cell_0_1425_end:
__sbr_cell_0_1426:
    lea rbx, [rbx+r8*4+0]
__sbr_cell_0_1426_end:
ff_aac_sbr_apply.L81b7_1:
__sbr_cell_0_1427:
    mov r14d, 137624
__sbr_cell_0_1427_end:
__sbr_cell_0_1428:
    .nops 1
__sbr_cell_0_1428_end:
ff_aac_sbr_apply.L8200:
__sbr_cell_0_1429:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1429_end:
__sbr_cell_0_1430:
    add r13d, 4294829672
__sbr_cell_0_1430_end:
__sbr_cell_0_1431:
    cmp r13d, 47
__sbr_cell_0_1431_end:
__sbr_cell_0_1432:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1432_end:
__sbr_cell_0_1433:
    vmovss xmm0, DWORD PTR [rdx+8]
__sbr_cell_0_1433_end:
__sbr_cell_0_1434:
    vmovss DWORD PTR [rbx+r14*4+0], xmm0
__sbr_cell_0_1434_end:
__sbr_cell_0_1435:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1435_end:
__sbr_cell_0_1436:
    add r13d, 4294829673
__sbr_cell_0_1436_end:
__sbr_cell_0_1437:
    cmp r13d, 47
__sbr_cell_0_1437_end:
__sbr_cell_0_1438:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1438_end:
__sbr_cell_0_1439:
    vmovss DWORD PTR [r11+r14*4+0], xmm0
__sbr_cell_0_1439_end:
__sbr_cell_0_1440:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1440_end:
__sbr_cell_0_1441:
    add r13d, 4294829674
__sbr_cell_0_1441_end:
__sbr_cell_0_1442:
    cmp r13d, 47
__sbr_cell_0_1442_end:
__sbr_cell_0_1443:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1443_end:
ff_aac_sbr_apply.L8200_1:
__sbr_cell_0_1444:
    vmovss DWORD PTR [r10+r14*4+0], xmm0
__sbr_cell_0_1444_end:
__sbr_cell_0_1445:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1445_end:
__sbr_cell_0_1446:
    add r13d, 4294829675
__sbr_cell_0_1446_end:
__sbr_cell_0_1447:
    cmp r13d, 47
__sbr_cell_0_1447_end:
__sbr_cell_0_1448:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1448_end:
__sbr_cell_0_1449:
    vmovss DWORD PTR [r9+r14*4+0], xmm0
__sbr_cell_0_1449_end:
__sbr_cell_0_1450:
    lea r13, [rdi+r14*1+0]
__sbr_cell_0_1450_end:
__sbr_cell_0_1451:
    add r13, 4
__sbr_cell_0_1451_end:
__sbr_cell_0_1452:
    add r14, 4
__sbr_cell_0_1452_end:
__sbr_cell_0_1453:
    cmp r13, 137624
__sbr_cell_0_1453_end:
__sbr_cell_0_1454:
    jne ff_aac_sbr_apply.L8200
__sbr_cell_0_1454_end:
ff_aac_sbr_apply.L828a:
__sbr_cell_0_1455:
    cmp ecx, 3
__sbr_cell_0_1455_end:
__sbr_cell_0_1456:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1456_end:
__sbr_cell_0_1457:
    je ff_aac_sbr_apply.L8520
__sbr_cell_0_1457_end:
__sbr_cell_0_1458:
    movzx edi, WORD PTR [r8+478222]
__sbr_cell_0_1458_end:
__sbr_cell_0_1459:
    cmp si, di
__sbr_cell_0_1459_end:
__sbr_cell_0_1460:
    jae ff_aac_sbr_apply.L83ca
__sbr_cell_0_1460_end:
__sbr_cell_0_1461:
    mov r8, rdi
__sbr_cell_0_1461_end:
__sbr_cell_0_1462:
    sub r8, rsi
__sbr_cell_0_1462_end:
__sbr_cell_0_1463:
    mov r9, r8
__sbr_cell_0_1463_end:
__sbr_cell_0_1464:
    and r9, 3
__sbr_cell_0_1464_end:
__sbr_cell_0_1465:
    je ff_aac_sbr_apply.L82f7
__sbr_cell_0_1465_end:
__sbr_cell_0_1466:
    mov r10d, esi
__sbr_cell_0_1466_end:
__sbr_cell_0_1467:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1467_end:
__sbr_cell_0_1468:
    neg r9
__sbr_cell_0_1468_end:
__sbr_cell_0_1469:
    xor r11d, r11d
__sbr_cell_0_1469_end:
__sbr_cell_0_1470:
    .nops 1
__sbr_cell_0_1470_end:
ff_aac_sbr_apply.L82d0:
__sbr_cell_0_1471:
    cmp r10d, 47
__sbr_cell_0_1471_end:
__sbr_cell_0_1472:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1472_end:
__sbr_cell_0_1473:
    vmovss xmm0, DWORD PTR [rdx+12]
__sbr_cell_0_1473_end:
__sbr_cell_0_1474:
    mov rbx, QWORD PTR [rbp-88]
__sbr_cell_0_1474_end:
__sbr_cell_0_1475:
    vmovss DWORD PTR [rbx+r10*4+0], xmm0
__sbr_cell_0_1475_end:
__sbr_cell_0_1476:
    dec r11
__sbr_cell_0_1476_end:
__sbr_cell_0_1477:
    inc r10
__sbr_cell_0_1477_end:
__sbr_cell_0_1478:
    cmp r9, r11
__sbr_cell_0_1478_end:
__sbr_cell_0_1479:
    jne ff_aac_sbr_apply.L82d0
__sbr_cell_0_1479_end:
__sbr_cell_0_1480:
    sub rsi, r11
__sbr_cell_0_1480_end:
ff_aac_sbr_apply.L82f7:
__sbr_cell_0_1481:
    dec r8
__sbr_cell_0_1481_end:
__sbr_cell_0_1482:
    cmp r8, 3
__sbr_cell_0_1482_end:
__sbr_cell_0_1483:
    jb ff_aac_sbr_apply.L83ca
__sbr_cell_0_1483_end:
__sbr_cell_0_1484:
    mov r8d, esi
__sbr_cell_0_1484_end:
__sbr_cell_0_1485:
    sub r8d, DWORD PTR [rbp-48]
__sbr_cell_0_1485_end:
__sbr_cell_0_1486:
    lea r9d, [r8+3]
__sbr_cell_0_1486_end:
__sbr_cell_0_1487:
    mov rbx, QWORD PTR [rbp-96]
__sbr_cell_0_1487_end:
__sbr_cell_0_1488:
    lea r9, [rbx+r9*4+0]
__sbr_cell_0_1488_end:
__sbr_cell_0_1489:
    lea r10d, [r8+2]
__sbr_cell_0_1489_end:
__sbr_cell_0_1490:
    lea r10, [rbx+r10*4+0]
__sbr_cell_0_1490_end:
__sbr_cell_0_1491:
    mov r11d, r8d
__sbr_cell_0_1491_end:
__sbr_cell_0_1492:
    inc r11d
__sbr_cell_0_1492_end:
__sbr_cell_0_1493:
    lea r11, [rbx+r11*4+0]
__sbr_cell_0_1493_end:
__sbr_cell_0_1494:
    sub rsi, rdi
__sbr_cell_0_1494_end:
__sbr_cell_0_1495:
    lea rbx, [rbx+r8*4+0]
__sbr_cell_0_1495_end:
ff_aac_sbr_apply.L82f7_1:
__sbr_cell_0_1496:
    mov r14d, 137624
__sbr_cell_0_1496_end:
__sbr_cell_0_1497:
    .nops 1
__sbr_cell_0_1497_end:
ff_aac_sbr_apply.L8340:
__sbr_cell_0_1498:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1498_end:
__sbr_cell_0_1499:
    add r13d, 4294829672
__sbr_cell_0_1499_end:
__sbr_cell_0_1500:
    cmp r13d, 47
__sbr_cell_0_1500_end:
__sbr_cell_0_1501:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1501_end:
__sbr_cell_0_1502:
    vmovss xmm0, DWORD PTR [rdx+12]
__sbr_cell_0_1502_end:
__sbr_cell_0_1503:
    vmovss DWORD PTR [rbx+r14*4+0], xmm0
__sbr_cell_0_1503_end:
__sbr_cell_0_1504:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1504_end:
__sbr_cell_0_1505:
    add r13d, 4294829673
__sbr_cell_0_1505_end:
__sbr_cell_0_1506:
    cmp r13d, 47
__sbr_cell_0_1506_end:
__sbr_cell_0_1507:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1507_end:
__sbr_cell_0_1508:
    vmovss DWORD PTR [r11+r14*4+0], xmm0
__sbr_cell_0_1508_end:
__sbr_cell_0_1509:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1509_end:
__sbr_cell_0_1510:
    add r13d, 4294829674
__sbr_cell_0_1510_end:
__sbr_cell_0_1511:
    cmp r13d, 47
__sbr_cell_0_1511_end:
__sbr_cell_0_1512:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1512_end:
ff_aac_sbr_apply.L8340_1:
__sbr_cell_0_1513:
    vmovss DWORD PTR [r10+r14*4+0], xmm0
__sbr_cell_0_1513_end:
__sbr_cell_0_1514:
    lea r13d, [r8+r14*1+0]
__sbr_cell_0_1514_end:
__sbr_cell_0_1515:
    add r13d, 4294829675
__sbr_cell_0_1515_end:
__sbr_cell_0_1516:
    cmp r13d, 47
__sbr_cell_0_1516_end:
__sbr_cell_0_1517:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1517_end:
__sbr_cell_0_1518:
    vmovss DWORD PTR [r9+r14*4+0], xmm0
__sbr_cell_0_1518_end:
__sbr_cell_0_1519:
    lea r13, [rsi+r14*1+0]
__sbr_cell_0_1519_end:
__sbr_cell_0_1520:
    add r13, 4
__sbr_cell_0_1520_end:
__sbr_cell_0_1521:
    add r14, 4
__sbr_cell_0_1521_end:
__sbr_cell_0_1522:
    cmp r13, 137624
__sbr_cell_0_1522_end:
__sbr_cell_0_1523:
    jne ff_aac_sbr_apply.L8340
__sbr_cell_0_1523_end:
ff_aac_sbr_apply.L83ca:
__sbr_cell_0_1524:
    cmp ecx, 4
__sbr_cell_0_1524_end:
__sbr_cell_0_1525:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1525_end:
__sbr_cell_0_1526:
    je ff_aac_sbr_apply.L8520
__sbr_cell_0_1526_end:
__sbr_cell_0_1527:
    movzx esi, WORD PTR [r8+478224]
__sbr_cell_0_1527_end:
__sbr_cell_0_1528:
    cmp di, si
__sbr_cell_0_1528_end:
__sbr_cell_0_1529:
    jae ff_aac_sbr_apply.L8509
__sbr_cell_0_1529_end:
__sbr_cell_0_1530:
    mov r8, rsi
__sbr_cell_0_1530_end:
__sbr_cell_0_1531:
    sub r8, rdi
__sbr_cell_0_1531_end:
__sbr_cell_0_1532:
    mov r9, r8
__sbr_cell_0_1532_end:
__sbr_cell_0_1533:
    and r9, 3
__sbr_cell_0_1533_end:
__sbr_cell_0_1534:
    je ff_aac_sbr_apply.L8437
__sbr_cell_0_1534_end:
__sbr_cell_0_1535:
    mov r10d, edi
__sbr_cell_0_1535_end:
__sbr_cell_0_1536:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1536_end:
__sbr_cell_0_1537:
    neg r9
__sbr_cell_0_1537_end:
__sbr_cell_0_1538:
    xor r11d, r11d
__sbr_cell_0_1538_end:
__sbr_cell_0_1539:
    .nops 1
__sbr_cell_0_1539_end:
ff_aac_sbr_apply.L8410:
__sbr_cell_0_1540:
    cmp r10d, 47
__sbr_cell_0_1540_end:
__sbr_cell_0_1541:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1541_end:
__sbr_cell_0_1542:
    vmovss xmm0, DWORD PTR [rdx+16]
__sbr_cell_0_1542_end:
__sbr_cell_0_1543:
    mov rbx, QWORD PTR [rbp-88]
__sbr_cell_0_1543_end:
__sbr_cell_0_1544:
    vmovss DWORD PTR [rbx+r10*4+0], xmm0
__sbr_cell_0_1544_end:
__sbr_cell_0_1545:
    dec r11
__sbr_cell_0_1545_end:
__sbr_cell_0_1546:
    inc r10
__sbr_cell_0_1546_end:
__sbr_cell_0_1547:
    cmp r9, r11
__sbr_cell_0_1547_end:
__sbr_cell_0_1548:
    jne ff_aac_sbr_apply.L8410
__sbr_cell_0_1548_end:
__sbr_cell_0_1549:
    sub rdi, r11
__sbr_cell_0_1549_end:
ff_aac_sbr_apply.L8437:
__sbr_cell_0_1550:
    dec r8
__sbr_cell_0_1550_end:
__sbr_cell_0_1551:
    cmp r8, 3
__sbr_cell_0_1551_end:
__sbr_cell_0_1552:
    jb ff_aac_sbr_apply.L8509
__sbr_cell_0_1552_end:
__sbr_cell_0_1553:
    mov r8d, edi
__sbr_cell_0_1553_end:
__sbr_cell_0_1554:
    sub r8d, DWORD PTR [rbp-48]
__sbr_cell_0_1554_end:
__sbr_cell_0_1555:
    lea r9d, [r8+3]
__sbr_cell_0_1555_end:
__sbr_cell_0_1556:
    mov rbx, QWORD PTR [rbp-96]
__sbr_cell_0_1556_end:
__sbr_cell_0_1557:
    lea r9, [rbx+r9*4+0]
__sbr_cell_0_1557_end:
__sbr_cell_0_1558:
    lea r10d, [r8+2]
__sbr_cell_0_1558_end:
__sbr_cell_0_1559:
    lea r10, [rbx+r10*4+0]
__sbr_cell_0_1559_end:
__sbr_cell_0_1560:
    mov r11d, r8d
__sbr_cell_0_1560_end:
__sbr_cell_0_1561:
    inc r11d
__sbr_cell_0_1561_end:
__sbr_cell_0_1562:
    lea r11, [rbx+r11*4+0]
__sbr_cell_0_1562_end:
__sbr_cell_0_1563:
    sub rdi, rsi
__sbr_cell_0_1563_end:
__sbr_cell_0_1564:
    lea rsi, [rbx+r8*4+0]
__sbr_cell_0_1564_end:
ff_aac_sbr_apply.L8437_1:
__sbr_cell_0_1565:
    mov ebx, 137624
__sbr_cell_0_1565_end:
__sbr_cell_0_1566:
    .nops 1
__sbr_cell_0_1566_end:
ff_aac_sbr_apply.L8480:
__sbr_cell_0_1567:
    lea r14d, [r8+rbx*1+0]
__sbr_cell_0_1567_end:
__sbr_cell_0_1568:
    add r14d, 4294829672
__sbr_cell_0_1568_end:
__sbr_cell_0_1569:
    cmp r14d, 47
__sbr_cell_0_1569_end:
__sbr_cell_0_1570:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1570_end:
__sbr_cell_0_1571:
    vmovss xmm0, DWORD PTR [rdx+16]
__sbr_cell_0_1571_end:
__sbr_cell_0_1572:
    vmovss DWORD PTR [rsi+rbx*4+0], xmm0
__sbr_cell_0_1572_end:
__sbr_cell_0_1573:
    lea r14d, [r8+rbx*1+0]
__sbr_cell_0_1573_end:
__sbr_cell_0_1574:
    add r14d, 4294829673
__sbr_cell_0_1574_end:
__sbr_cell_0_1575:
    cmp r14d, 47
__sbr_cell_0_1575_end:
__sbr_cell_0_1576:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1576_end:
__sbr_cell_0_1577:
    vmovss DWORD PTR [r11+rbx*4+0], xmm0
__sbr_cell_0_1577_end:
__sbr_cell_0_1578:
    lea r14d, [r8+rbx*1+0]
__sbr_cell_0_1578_end:
__sbr_cell_0_1579:
    add r14d, 4294829674
__sbr_cell_0_1579_end:
__sbr_cell_0_1580:
    cmp r14d, 47
__sbr_cell_0_1580_end:
__sbr_cell_0_1581:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1581_end:
ff_aac_sbr_apply.L8480_1:
__sbr_cell_0_1582:
    vmovss DWORD PTR [r10+rbx*4+0], xmm0
__sbr_cell_0_1582_end:
__sbr_cell_0_1583:
    lea r14d, [r8+rbx*1+0]
__sbr_cell_0_1583_end:
__sbr_cell_0_1584:
    add r14d, 4294829675
__sbr_cell_0_1584_end:
__sbr_cell_0_1585:
    cmp r14d, 47
__sbr_cell_0_1585_end:
__sbr_cell_0_1586:
    ja ff_aac_sbr_apply.L9b40
__sbr_cell_0_1586_end:
__sbr_cell_0_1587:
    vmovss DWORD PTR [r9+rbx*4+0], xmm0
__sbr_cell_0_1587_end:
__sbr_cell_0_1588:
    lea r14, [rdi+rbx*1+0]
__sbr_cell_0_1588_end:
__sbr_cell_0_1589:
    add r14, 4
__sbr_cell_0_1589_end:
__sbr_cell_0_1590:
    add rbx, 4
__sbr_cell_0_1590_end:
__sbr_cell_0_1591:
    cmp r14, 137624
__sbr_cell_0_1591_end:
__sbr_cell_0_1592:
    jne ff_aac_sbr_apply.L8480
__sbr_cell_0_1592_end:
ff_aac_sbr_apply.L8509:
__sbr_cell_0_1593:
    cmp ecx, 5
__sbr_cell_0_1593_end:
__sbr_cell_0_1594:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1594_end:
__sbr_cell_0_1595:
    jne ff_aac_sbr_apply.L9c18
__sbr_cell_0_1595_end:
__sbr_cell_0_1596:
    .nops 1
__sbr_cell_0_1596_end:
ff_aac_sbr_apply.L8520:
__sbr_cell_0_1597:
    cmp DWORD PTR [r8+477956], 0
__sbr_cell_0_1597_end:
__sbr_cell_0_1598:
    mov r11d, 0
__sbr_cell_0_1598_end:
__sbr_cell_0_1599:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_1599_end:
__sbr_cell_0_1600:
    mov r14, QWORD PTR [rbp-128]
__sbr_cell_0_1600_end:
__sbr_cell_0_1601:
    mov r13, QWORD PTR [rbp-232]
__sbr_cell_0_1601_end:
__sbr_cell_0_1602:
    je ff_aac_sbr_apply.L8660
__sbr_cell_0_1602_end:
__sbr_cell_0_1603:
    cmp DWORD PTR [rbx+4], 0
__sbr_cell_0_1603_end:
__sbr_cell_0_1604:
    je ff_aac_sbr_apply.L8660
__sbr_cell_0_1604_end:
__sbr_cell_0_1605:
    mov rcx, QWORD PTR [rbp-104]
__sbr_cell_0_1605_end:
__sbr_cell_0_1606:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_0_1606_end:
__sbr_cell_0_1607:
    shl rcx, 4
__sbr_cell_0_1607_end:
__sbr_cell_0_1608:
    add rcx, r14
__sbr_cell_0_1608_end:
__sbr_cell_0_1609:
    mov edx, 1
__sbr_cell_0_1609_end:
__sbr_cell_0_1610:
    mov rsi, QWORD PTR [rbp-408]
__sbr_cell_0_1610_end:
__sbr_cell_0_1611:
    xor edi, edi
__sbr_cell_0_1611_end:
__sbr_cell_0_1612:
    .nops 1
__sbr_cell_0_1612_end:
ff_aac_sbr_apply.L8570:
__sbr_cell_0_1613:
    movzx r8d, WORD PTR [rsi-4]
__sbr_cell_0_1613_end:
__sbr_cell_0_1614:
    movzx r10d, WORD PTR [rsi-2]
__sbr_cell_0_1614_end:
__sbr_cell_0_1615:
    add r10d, r8d
__sbr_cell_0_1615_end:
__sbr_cell_0_1616:
    shr r10d, 1
__sbr_cell_0_1616_end:
__sbr_cell_0_1617:
    movzx r9d, BYTE PTR [r13+rdi*1-1]
__sbr_cell_0_1617_end:
__sbr_cell_0_1618:
    movsxd r8, DWORD PTR [rbx+14600]
__sbr_cell_0_1618_end:
__sbr_cell_0_1619:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1619_end:
__sbr_cell_0_1620:
    cmp rax, r8
__sbr_cell_0_1620_end:
__sbr_cell_0_1621:
    jge ff_aac_sbr_apply.L85c0
__sbr_cell_0_1621_end:
__sbr_cell_0_1622:
    cmp r10d, 48
__sbr_cell_0_1622_end:
__sbr_cell_0_1623:
    jae ff_aac_sbr_apply.L9b68
__sbr_cell_0_1623_end:
__sbr_cell_0_1624:
    mov r10d, r10d
__sbr_cell_0_1624_end:
__sbr_cell_0_1625:
    cmp BYTE PTR [r14+r10*1+0], 1
__sbr_cell_0_1625_end:
__sbr_cell_0_1626:
    movzx r9d, r9b
__sbr_cell_0_1626_end:
__sbr_cell_0_1627:
    cmovne r9d, r11d
__sbr_cell_0_1627_end:
ff_aac_sbr_apply.L8570_1:
__sbr_cell_0_1628:
    jmp ff_aac_sbr_apply.L85cd
__sbr_cell_0_1628_end:
__sbr_cell_0_1629:
    .nops 1
__sbr_cell_0_1629_end:
ff_aac_sbr_apply.L85c0:
__sbr_cell_0_1630:
    cmp r10d, 47
__sbr_cell_0_1630_end:
__sbr_cell_0_1631:
    ja ff_aac_sbr_apply.L9b54
__sbr_cell_0_1631_end:
__sbr_cell_0_1632:
    mov r10d, r10d
__sbr_cell_0_1632_end:
ff_aac_sbr_apply.L85cd:
__sbr_cell_0_1633:
    mov BYTE PTR [rcx+r10*1+0], r9b
__sbr_cell_0_1633_end:
ff_aac_sbr_apply.L85cd_1:
__sbr_cell_0_1634:
    mov r9, QWORD PTR [rbp-56]
__sbr_cell_0_1634_end:
__sbr_cell_0_1635:
    mov r9d, DWORD PTR [r9+477956]
__sbr_cell_0_1635_end:
__sbr_cell_0_1636:
    cmp rdx, r9
__sbr_cell_0_1636_end:
__sbr_cell_0_1637:
    jae ff_aac_sbr_apply.L8660
__sbr_cell_0_1637_end:
__sbr_cell_0_1638:
    movzx r9d, WORD PTR [rsi-2]
__sbr_cell_0_1638_end:
__sbr_cell_0_1639:
    movzx r10d, WORD PTR [rsi+0]
__sbr_cell_0_1639_end:
__sbr_cell_0_1640:
    add r10d, r9d
__sbr_cell_0_1640_end:
__sbr_cell_0_1641:
    shr r10d, 1
__sbr_cell_0_1641_end:
__sbr_cell_0_1642:
    movzx r9d, BYTE PTR [r13+rdi*1+0]
__sbr_cell_0_1642_end:
__sbr_cell_0_1643:
    sub r10d, DWORD PTR [rbp-48]
__sbr_cell_0_1643_end:
__sbr_cell_0_1644:
    cmp rax, r8
__sbr_cell_0_1644_end:
__sbr_cell_0_1645:
    jge ff_aac_sbr_apply.L8620
__sbr_cell_0_1645_end:
__sbr_cell_0_1646:
    cmp r10d, 47
__sbr_cell_0_1646_end:
__sbr_cell_0_1647:
    ja ff_aac_sbr_apply.L9b68
__sbr_cell_0_1647_end:
__sbr_cell_0_1648:
    mov r8d, r10d
__sbr_cell_0_1648_end:
ff_aac_sbr_apply.L85cd_2:
__sbr_cell_0_1649:
    cmp BYTE PTR [r14+r8*1+0], 1
__sbr_cell_0_1649_end:
__sbr_cell_0_1650:
    movzx r9d, r9b
__sbr_cell_0_1650_end:
__sbr_cell_0_1651:
    cmovne r9d, r11d
__sbr_cell_0_1651_end:
__sbr_cell_0_1652:
    jmp ff_aac_sbr_apply.L862d
__sbr_cell_0_1652_end:
__sbr_cell_0_1653:
    .nops 1
__sbr_cell_0_1653_end:
ff_aac_sbr_apply.L8620:
__sbr_cell_0_1654:
    cmp r10d, 47
__sbr_cell_0_1654_end:
__sbr_cell_0_1655:
    ja ff_aac_sbr_apply.L9b54
__sbr_cell_0_1655_end:
__sbr_cell_0_1656:
    mov r8d, r10d
__sbr_cell_0_1656_end:
ff_aac_sbr_apply.L862d:
__sbr_cell_0_1657:
    mov BYTE PTR [rcx+r8*1+0], r9b
__sbr_cell_0_1657_end:
__sbr_cell_0_1658:
    add rdi, 2
__sbr_cell_0_1658_end:
ff_aac_sbr_apply.L862d_1:
__sbr_cell_0_1659:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1659_end:
__sbr_cell_0_1660:
    mov r8d, DWORD PTR [r8+477956]
__sbr_cell_0_1660_end:
__sbr_cell_0_1661:
    cmp rdi, r8
__sbr_cell_0_1661_end:
__sbr_cell_0_1662:
    jae ff_aac_sbr_apply.L8660
__sbr_cell_0_1662_end:
__sbr_cell_0_1663:
    add rdx, 2
__sbr_cell_0_1663_end:
__sbr_cell_0_1664:
    add rsi, 4
__sbr_cell_0_1664_end:
__sbr_cell_0_1665:
    cmp rdi, 48
__sbr_cell_0_1665_end:
__sbr_cell_0_1666:
    jne ff_aac_sbr_apply.L8570
__sbr_cell_0_1666_end:
__sbr_cell_0_1667:
    jmp ff_aac_sbr_apply.L9b59
__sbr_cell_0_1667_end:
__sbr_cell_0_1668:
    .nops 1
__sbr_cell_0_1668_end:
ff_aac_sbr_apply.L8660:
__sbr_cell_0_1669:
    cmp QWORD PTR [rbp-80], 0
__sbr_cell_0_1669_end:
__sbr_cell_0_1670:
    je ff_aac_sbr_apply.L8740
__sbr_cell_0_1670_end:
__sbr_cell_0_1671:
    mov rcx, QWORD PTR [rbp-104]
__sbr_cell_0_1671_end:
__sbr_cell_0_1672:
    lea rbx, [rcx+rcx*2+0]
__sbr_cell_0_1672_end:
__sbr_cell_0_1673:
    shl rbx, 4
__sbr_cell_0_1673_end:
__sbr_cell_0_1674:
    add rbx, QWORD PTR [rbp-128]
__sbr_cell_0_1674_end:
__sbr_cell_0_1675:
    lea r14, [rax+rax*2+0]
__sbr_cell_0_1675_end:
__sbr_cell_0_1676:
    shl r14, 4
__sbr_cell_0_1676_end:
__sbr_cell_0_1677:
    add r14, QWORD PTR [rbp-424]
__sbr_cell_0_1677_end:
__sbr_cell_0_1678:
    mov eax, DWORD PTR [rbp-48]
__sbr_cell_0_1678_end:
__sbr_cell_0_1679:
    neg eax
__sbr_cell_0_1679_end:
__sbr_cell_0_1680:
    mov QWORD PTR [rbp-120], rax
__sbr_cell_0_1680_end:
__sbr_cell_0_1681:
    xor r13d, r13d
__sbr_cell_0_1681_end:
__sbr_cell_0_1682:
    jmp ff_aac_sbr_apply.L86d7
__sbr_cell_0_1682_end:
__sbr_cell_0_1683:
    .nops 1
__sbr_cell_0_1683_end:
ff_aac_sbr_apply.L86a0:
__sbr_cell_0_1684:
    xor esi, esi
__sbr_cell_0_1684_end:
__sbr_cell_0_1685:
    mov edx, eax
__sbr_cell_0_1685_end:
__sbr_cell_0_1686:
    sub edx, DWORD PTR [rbp-48]
__sbr_cell_0_1686_end:
__sbr_cell_0_1687:
    cmp edx, 49
__sbr_cell_0_1687_end:
__sbr_cell_0_1688:
    jae ff_aac_sbr_apply.L9b4f
__sbr_cell_0_1688_end:
ff_aac_sbr_apply.L86b0:
__sbr_cell_0_1689:
    inc r13
__sbr_cell_0_1689_end:
__sbr_cell_0_1690:
    mov edi, edx
__sbr_cell_0_1690_end:
__sbr_cell_0_1691:
    add rdi, r14
__sbr_cell_0_1691_end:
__sbr_cell_0_1692:
    sub ecx, eax
__sbr_cell_0_1692_end:
__sbr_cell_0_1693:
    movsxd rdx, ecx
__sbr_cell_0_1693_end:
__sbr_cell_0_1694:
    movzx esi, sil
__sbr_cell_0_1694_end:
__sbr_cell_0_1695:
    vzeroupper
__sbr_cell_0_1695_end:
__sbr_cell_0_1696:
    call memset
__sbr_cell_0_1696_end:
ff_aac_sbr_apply.L86b0_1:
__sbr_cell_0_1697:
    cmp r13, QWORD PTR [rbp-80]
__sbr_cell_0_1697_end:
__sbr_cell_0_1698:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_1698_end:
__sbr_cell_0_1699:
    je ff_aac_sbr_apply.L8740
__sbr_cell_0_1699_end:
ff_aac_sbr_apply.L86d7:
__sbr_cell_0_1700:
    movzx eax, WORD PTR [r15+r13*2+0]
__sbr_cell_0_1700_end:
__sbr_cell_0_1701:
    movzx ecx, WORD PTR [r15+r13*2+2]
__sbr_cell_0_1701_end:
__sbr_cell_0_1702:
    cmp ax, cx
__sbr_cell_0_1702_end:
__sbr_cell_0_1703:
    jae ff_aac_sbr_apply.L86a0
__sbr_cell_0_1703_end:
__sbr_cell_0_1704:
    mov edx, ecx
__sbr_cell_0_1704_end:
__sbr_cell_0_1705:
    sub rdx, rax
__sbr_cell_0_1705_end:
__sbr_cell_0_1706:
    mov rsi, QWORD PTR [rbp-120]
__sbr_cell_0_1706_end:
__sbr_cell_0_1707:
    add esi, eax
__sbr_cell_0_1707_end:
__sbr_cell_0_1708:
    .nops 1
__sbr_cell_0_1708_end:
ff_aac_sbr_apply.L8700:
__sbr_cell_0_1709:
    cmp esi, 48
__sbr_cell_0_1709_end:
__sbr_cell_0_1710:
    jae ff_aac_sbr_apply.L9b36
__sbr_cell_0_1710_end:
__sbr_cell_0_1711:
    mov edi, esi
__sbr_cell_0_1711_end:
__sbr_cell_0_1712:
    cmp BYTE PTR [rbx+rdi*1+0], 0
__sbr_cell_0_1712_end:
__sbr_cell_0_1713:
    jne ff_aac_sbr_apply.L8720
__sbr_cell_0_1713_end:
__sbr_cell_0_1714:
    inc esi
__sbr_cell_0_1714_end:
__sbr_cell_0_1715:
    dec rdx
__sbr_cell_0_1715_end:
__sbr_cell_0_1716:
    jne ff_aac_sbr_apply.L8700
__sbr_cell_0_1716_end:
__sbr_cell_0_1717:
    jmp ff_aac_sbr_apply.L86a0
__sbr_cell_0_1717_end:
__sbr_cell_0_1718:
    .nops 1
__sbr_cell_0_1718_end:
ff_aac_sbr_apply.L8720:
__sbr_cell_0_1719:
    mov sil, 1
__sbr_cell_0_1719_end:
__sbr_cell_0_1720:
    mov edx, eax
__sbr_cell_0_1720_end:
__sbr_cell_0_1721:
    sub edx, DWORD PTR [rbp-48]
__sbr_cell_0_1721_end:
__sbr_cell_0_1722:
    cmp edx, 49
__sbr_cell_0_1722_end:
__sbr_cell_0_1723:
    jb ff_aac_sbr_apply.L86b0
__sbr_cell_0_1723_end:
__sbr_cell_0_1724:
    jmp ff_aac_sbr_apply.L9b4f
__sbr_cell_0_1724_end:
__sbr_cell_0_1725:
    .nops 1
__sbr_cell_0_1725_end:
ff_aac_sbr_apply.L8740:
__sbr_cell_0_1726:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_1726_end:
__sbr_cell_0_1727:
    mov eax, DWORD PTR [rbx+8]
__sbr_cell_0_1727_end:
__sbr_cell_0_1728:
    mov rdx, QWORD PTR [rbp-104]
__sbr_cell_0_1728_end:
__sbr_cell_0_1729:
    cmp rdx, rax
__sbr_cell_0_1729_end:
__sbr_cell_0_1730:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1730_end:
__sbr_cell_0_1731:
    jae ff_aac_sbr_apply.L8818
__sbr_cell_0_1731_end:
__sbr_cell_0_1732:
    lea rcx, [rdx+1]
__sbr_cell_0_1732_end:
__sbr_cell_0_1733:
    add r12, 192
__sbr_cell_0_1733_end:
__sbr_cell_0_1734:
    add QWORD PTR [rbp-88], 192
__sbr_cell_0_1734_end:
ff_aac_sbr_apply.L8740_1:
__sbr_cell_0_1735:
    add QWORD PTR [rbp-96], 192
__sbr_cell_0_1735_end:
__sbr_cell_0_1736:
    mov rax, rdx
__sbr_cell_0_1736_end:
__sbr_cell_0_1737:
    cmp rdx, 8
__sbr_cell_0_1737_end:
__sbr_cell_0_1738:
    jne ff_aac_sbr_apply.L7db0
__sbr_cell_0_1738_end:
__sbr_cell_0_1739:
    jmp ff_aac_sbr_apply.L9b7c
__sbr_cell_0_1739_end:
__sbr_cell_0_1740:
    .nops 1
__sbr_cell_0_1740_end:
ff_aac_sbr_apply.L8790:
__sbr_cell_0_1741:
    mov eax, DWORD PTR [r8+166264]
__sbr_cell_0_1741_end:
__sbr_cell_0_1742:
    mov DWORD PTR [rbp-48], eax
__sbr_cell_0_1742_end:
__sbr_cell_0_1743:
    xor eax, eax
__sbr_cell_0_1743_end:
__sbr_cell_0_1744:
    jmp ff_aac_sbr_apply.L881c
__sbr_cell_0_1744_end:
ff_aac_sbr_apply.L879e:
__sbr_cell_0_1745:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_0_1745_end:
__sbr_cell_0_1746:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_0_1746_end:
__sbr_cell_0_1747:
    mov esi, 16
__sbr_cell_0_1747_end:
__sbr_cell_0_1748:
    lea rdx, [rip+L_str_36]
__sbr_cell_0_1748_end:
__sbr_cell_0_1749:
    xor eax, eax
__sbr_cell_0_1749_end:
__sbr_cell_0_1750:
    vzeroupper
__sbr_cell_0_1750_end:
__sbr_cell_0_1751:
    call av_log
__sbr_cell_0_1751_end:
ff_aac_sbr_apply.L879e_1:
__sbr_cell_0_1752:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_1752_end:
__sbr_cell_0_1753:
    mov QWORD PTR [rax+166180], 0
__sbr_cell_0_1753_end:
__sbr_cell_0_1754:
    mov DWORD PTR [rax+166192], 0
__sbr_cell_0_1754_end:
__sbr_cell_0_1755:
    mov DWORD PTR [rax+166264], 32
__sbr_cell_0_1755_end:
__sbr_cell_0_1756:
    mov DWORD PTR [rax+166272], 0
__sbr_cell_0_1756_end:
__sbr_cell_0_1757:
    mov DWORD PTR [rax+269672], 4294967295
__sbr_cell_0_1757_end:
__sbr_cell_0_1758:
    mov DWORD PTR [rax+180904], 4294967295
__sbr_cell_0_1758_end:
ff_aac_sbr_apply.L879e_2:
__sbr_cell_0_1759:
    mov rax, QWORD PTR [rbp-360]
__sbr_cell_0_1759_end:
__sbr_cell_0_1760:
    mov WORD PTR [rax+4], 65535
__sbr_cell_0_1760_end:
__sbr_cell_0_1761:
    mov DWORD PTR [rax+0], 4294967295
__sbr_cell_0_1761_end:
__sbr_cell_0_1762:
    jmp ff_aac_sbr_apply.L9927
__sbr_cell_0_1762_end:
ff_aac_sbr_apply.L8818:
__sbr_cell_0_1763:
    mov r10, QWORD PTR [rbp-128]
__sbr_cell_0_1763_end:
ff_aac_sbr_apply.L881c:
__sbr_cell_0_1764:
    lea rcx, [rbx+14596]
__sbr_cell_0_1764_end:
__sbr_cell_0_1765:
    mov QWORD PTR [rbp-272], rcx
__sbr_cell_0_1765_end:
__sbr_cell_0_1766:
    mov ecx, eax
__sbr_cell_0_1766_end:
__sbr_cell_0_1767:
    lea rdx, [rcx+rcx*2+0]
__sbr_cell_0_1767_end:
__sbr_cell_0_1768:
    shl rdx, 4
__sbr_cell_0_1768_end:
__sbr_cell_0_1769:
    vmovups ymm0, YMMWORD PTR [r10+rdx*1+0]
__sbr_cell_0_1769_end:
__sbr_cell_0_1770:
    vmovups ymm1, YMMWORD PTR [r10+rdx*1+16]
__sbr_cell_0_1770_end:
__sbr_cell_0_1771:
    vmovups YMMWORD PTR [r10+16], ymm1
__sbr_cell_0_1771_end:
__sbr_cell_0_1772:
    vmovups YMMWORD PTR [r10+0], ymm0
__sbr_cell_0_1772_end:
ff_aac_sbr_apply.L881c_1:
__sbr_cell_0_1773:
    cmp DWORD PTR [r8+166228], 0
__sbr_cell_0_1773_end:
__sbr_cell_0_1774:
    je ff_aac_sbr_apply.L8947
__sbr_cell_0_1774_end:
__sbr_cell_0_1775:
    test eax, eax
__sbr_cell_0_1775_end:
__sbr_cell_0_1776:
    je ff_aac_sbr_apply.L98e0
__sbr_cell_0_1776_end:
__sbr_cell_0_1777:
    movzx r12d, BYTE PTR [rbx+88732]
__sbr_cell_0_1777_end:
__sbr_cell_0_1778:
    cmp r12d, 19
__sbr_cell_0_1778_end:
__sbr_cell_0_1779:
    jae ff_aac_sbr_apply.L914e
__sbr_cell_0_1779_end:
__sbr_cell_0_1780:
    movsxd rdx, DWORD PTR [rbp-48]
__sbr_cell_0_1780_end:
__sbr_cell_0_1781:
    lea r14, [rdx+rdx*4+0]
__sbr_cell_0_1781_end:
__sbr_cell_0_1782:
    shl r14, 6
__sbr_cell_0_1782_end:
__sbr_cell_0_1783:
    mov rdx, QWORD PTR [rbp-184]
__sbr_cell_0_1783_end:
__sbr_cell_0_1784:
    lea rdi, [rdx+r14*1+0]
__sbr_cell_0_1784_end:
__sbr_cell_0_1785:
    mov r8, QWORD PTR [rbp-56]
__sbr_cell_0_1785_end:
__sbr_cell_0_1786:
    cmp DWORD PTR [r8+166272], 0
__sbr_cell_0_1786_end:
__sbr_cell_0_1787:
    je ff_aac_sbr_apply.L8b6b
__sbr_cell_0_1787_end:
ff_aac_sbr_apply.L881c_2:
__sbr_cell_0_1788:
    movzx r15d, BYTE PTR [rbx+88733]
__sbr_cell_0_1788_end:
__sbr_cell_0_1789:
    sub r15d, r12d
__sbr_cell_0_1789_end:
__sbr_cell_0_1790:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_1790_end:
__sbr_cell_0_1791:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_1791_end:
__sbr_cell_0_1792:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_1792_end:
__sbr_cell_0_1793:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_1793_end:
__sbr_cell_0_1794:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_1794_end:
__sbr_cell_0_1795:
    add r15d, r15d
__sbr_cell_0_1795_end:
__sbr_cell_0_1796:
    mov QWORD PTR [rbp-80], rdi
__sbr_cell_0_1796_end:
ff_aac_sbr_apply.L881c_3:
__sbr_cell_0_1797:
    lea rdi, [rdi+rax*8+0]
__sbr_cell_0_1797_end:
__sbr_cell_0_1798:
    add rdi, 16
__sbr_cell_0_1798_end:
__sbr_cell_0_1799:
    mov esi, r15d
__sbr_cell_0_1799_end:
__sbr_cell_0_1800:
    mov r13, r8
__sbr_cell_0_1800_end:
__sbr_cell_0_1801:
    vzeroupper
__sbr_cell_0_1801_end:
__sbr_cell_0_1802:
    call QWORD PTR [r8+559880]
__sbr_cell_0_1802_end:
ff_aac_sbr_apply.L881c_4:
__sbr_cell_0_1803:
    shl r12d, 4
__sbr_cell_0_1803_end:
__sbr_cell_0_1804:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_1804_end:
__sbr_cell_0_1805:
    add rax, r14
__sbr_cell_0_1805_end:
__sbr_cell_0_1806:
    add r12, rax
__sbr_cell_0_1806_end:
__sbr_cell_0_1807:
    xor ebx, ebx
__sbr_cell_0_1807_end:
__sbr_cell_0_1808:
    .nops 1
__sbr_cell_0_1808_end:
ff_aac_sbr_apply.L8900:
__sbr_cell_0_1809:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_1809_end:
__sbr_cell_0_1810:
    vmovss DWORD PTR [r13+rbx*4+552416], xmm0
__sbr_cell_0_1810_end:
__sbr_cell_0_1811:
    inc rbx
__sbr_cell_0_1811_end:
ff_aac_sbr_apply.L8900_1:
__sbr_cell_0_1812:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_1812_end:
__sbr_cell_0_1813:
    cmp rbx, rax
__sbr_cell_0_1813_end:
__sbr_cell_0_1814:
    mov r8, r13
__sbr_cell_0_1814_end:
__sbr_cell_0_1815:
    jae ff_aac_sbr_apply.L8b2a
__sbr_cell_0_1815_end:
__sbr_cell_0_1816:
    mov rdi, r12
__sbr_cell_0_1816_end:
__sbr_cell_0_1817:
    mov esi, r15d
__sbr_cell_0_1817_end:
__sbr_cell_0_1818:
    mov r13, r8
__sbr_cell_0_1818_end:
__sbr_cell_0_1819:
    call QWORD PTR [r8+559880]
__sbr_cell_0_1819_end:
ff_aac_sbr_apply.L8900_2:
__sbr_cell_0_1820:
    add r12, 320
__sbr_cell_0_1820_end:
__sbr_cell_0_1821:
    cmp rbx, 48
__sbr_cell_0_1821_end:
__sbr_cell_0_1822:
    jne ff_aac_sbr_apply.L8900
__sbr_cell_0_1822_end:
__sbr_cell_0_1823:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_1823_end:
ff_aac_sbr_apply.L8947:
__sbr_cell_0_1824:
    test eax, eax
__sbr_cell_0_1824_end:
__sbr_cell_0_1825:
    je ff_aac_sbr_apply.L98e0
__sbr_cell_0_1825_end:
__sbr_cell_0_1826:
    movsxd rcx, DWORD PTR [rbp-48]
__sbr_cell_0_1826_end:
__sbr_cell_0_1827:
    mov QWORD PTR [rbp-96], rcx
__sbr_cell_0_1827_end:
__sbr_cell_0_1828:
    mov ecx, 1
__sbr_cell_0_1828_end:
ff_aac_sbr_apply.L8947_1:
__sbr_cell_0_1829:
    mov rsi, QWORD PTR [rbp-56]
__sbr_cell_0_1829_end:
__sbr_cell_0_1830:
    mov rdi, rsi
__sbr_cell_0_1830_end:
__sbr_cell_0_1831:
    xor r8d, r8d
__sbr_cell_0_1831_end:
__sbr_cell_0_1832:
    .nops 1
__sbr_cell_0_1832_end:
ff_aac_sbr_apply.L8970:
__sbr_cell_0_1833:
    movzx r9d, BYTE PTR [rbx+r8*1+88732]
__sbr_cell_0_1833_end:
__sbr_cell_0_1834:
    mov r8, rcx
__sbr_cell_0_1834_end:
__sbr_cell_0_1835:
    movzx ecx, BYTE PTR [rbx+rcx*1+12]
__sbr_cell_0_1835_end:
__sbr_cell_0_1836:
    mov rdx, QWORD PTR [rbp-176]
__sbr_cell_0_1836_end:
__sbr_cell_0_1837:
    lea r14, [rdx+311940]
__sbr_cell_0_1837_end:
__sbr_cell_0_1838:
    add rdx, 311890
__sbr_cell_0_1838_end:
__sbr_cell_0_1839:
    test cl, cl
__sbr_cell_0_1839_end:
__sbr_cell_0_1840:
    cmove r14, rdx
__sbr_cell_0_1840_end:
__sbr_cell_0_1841:
    cmp r9d, 18
__sbr_cell_0_1841_end:
__sbr_cell_0_1842:
    ja ff_aac_sbr_apply.L9146
__sbr_cell_0_1842_end:
__sbr_cell_0_1843:
    cmp cl, 1
__sbr_cell_0_1843_end:
__sbr_cell_0_1844:
    ja ff_aac_sbr_apply.L9a64
__sbr_cell_0_1844_end:
__sbr_cell_0_1845:
    mov rdx, r9
__sbr_cell_0_1845_end:
__sbr_cell_0_1846:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_0_1846_end:
__sbr_cell_0_1847:
    movzx r12d, BYTE PTR [rax+r8*1+88732]
__sbr_cell_0_1847_end:
ff_aac_sbr_apply.L8970_1:
__sbr_cell_0_1848:
    sub r12d, edx
__sbr_cell_0_1848_end:
__sbr_cell_0_1849:
    add r12d, r12d
__sbr_cell_0_1849_end:
__sbr_cell_0_1850:
    shl edx, 4
__sbr_cell_0_1850_end:
__sbr_cell_0_1851:
    add rdx, QWORD PTR [rbp-400]
__sbr_cell_0_1851_end:
__sbr_cell_0_1852:
    mov QWORD PTR [rbp-128], rdx
__sbr_cell_0_1852_end:
__sbr_cell_0_1853:
    xor ebx, ebx
__sbr_cell_0_1853_end:
__sbr_cell_0_1854:
    mov QWORD PTR [rbp-120], rdi
__sbr_cell_0_1854_end:
__sbr_cell_0_1855:
    mov QWORD PTR [rbp-104], r8
__sbr_cell_0_1855_end:
__sbr_cell_0_1856:
    jmp ff_aac_sbr_apply.L89f3
__sbr_cell_0_1856_end:
__sbr_cell_0_1857:
    .nops 1
__sbr_cell_0_1857_end:
ff_aac_sbr_apply.L89e0:
__sbr_cell_0_1858:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_0_1858_end:
__sbr_cell_0_1859:
    movzx ecx, BYTE PTR [rax+r8*1+12]
__sbr_cell_0_1859_end:
__sbr_cell_0_1860:
    cmp cl, 2
__sbr_cell_0_1860_end:
__sbr_cell_0_1861:
    jae ff_aac_sbr_apply.L9a64
__sbr_cell_0_1861_end:
ff_aac_sbr_apply.L89f3:
__sbr_cell_0_1862:
    movzx eax, cl
__sbr_cell_0_1862_end:
__sbr_cell_0_1863:
    mov eax, DWORD PTR [rsi+rax*4+477952]
__sbr_cell_0_1863_end:
__sbr_cell_0_1864:
    cmp rbx, rax
__sbr_cell_0_1864_end:
__sbr_cell_0_1865:
    jae ff_aac_sbr_apply.L8b00
__sbr_cell_0_1865_end:
__sbr_cell_0_1866:
    mov rdx, rbx
__sbr_cell_0_1866_end:
__sbr_cell_0_1867:
    inc rbx
__sbr_cell_0_1867_end:
__sbr_cell_0_1868:
    movzx eax, WORD PTR [r14+rdx*2+2]
__sbr_cell_0_1868_end:
__sbr_cell_0_1869:
    movzx r13d, WORD PTR [r14+rdx*2+0]
__sbr_cell_0_1869_end:
__sbr_cell_0_1870:
    cmp r13w, ax
__sbr_cell_0_1870_end:
__sbr_cell_0_1871:
    jae ff_aac_sbr_apply.L89e0
__sbr_cell_0_1871_end:
__sbr_cell_0_1872:
    mov QWORD PTR [rbp-88], rdx
__sbr_cell_0_1872_end:
__sbr_cell_0_1873:
    sub eax, r13d
__sbr_cell_0_1873_end:
__sbr_cell_0_1874:
    imul eax, r12d
__sbr_cell_0_1874_end:
__sbr_cell_0_1875:
    mov DWORD PTR [rbp-80], eax
__sbr_cell_0_1875_end:
__sbr_cell_0_1876:
    lea r15, [r13*4+0]
__sbr_cell_0_1876_end:
ff_aac_sbr_apply.L89f3_1:
__sbr_cell_0_1877:
    add r15, r13
__sbr_cell_0_1877_end:
__sbr_cell_0_1878:
    shl r15d, 6
__sbr_cell_0_1878_end:
__sbr_cell_0_1879:
    add r15, QWORD PTR [rbp-128]
__sbr_cell_0_1879_end:
__sbr_cell_0_1880:
    vxorps xmm1, xmm1, xmm1
__sbr_cell_0_1880_end:
__sbr_cell_0_1881:
    .nops 1
__sbr_cell_0_1881_end:
ff_aac_sbr_apply.L8a50:
__sbr_cell_0_1882:
    vmovss DWORD PTR [rbp-48], xmm1
__sbr_cell_0_1882_end:
__sbr_cell_0_1883:
    mov rdi, r15
__sbr_cell_0_1883_end:
__sbr_cell_0_1884:
    mov esi, r12d
__sbr_cell_0_1884_end:
ff_aac_sbr_apply.L8a50_1:
__sbr_cell_0_1885:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_1885_end:
__sbr_cell_0_1886:
    vzeroupper
__sbr_cell_0_1886_end:
__sbr_cell_0_1887:
    call QWORD PTR [rax+559880]
__sbr_cell_0_1887_end:
ff_aac_sbr_apply.L8a50_2:
__sbr_cell_0_1888:
    vmovss xmm1, DWORD PTR [rbp-48]
__sbr_cell_0_1888_end:
__sbr_cell_0_1889:
    mov rsi, QWORD PTR [rbp-56]
__sbr_cell_0_1889_end:
__sbr_cell_0_1890:
    vaddss xmm1, xmm1, xmm0
__sbr_cell_0_1890_end:
__sbr_cell_0_1891:
    inc r13
__sbr_cell_0_1891_end:
__sbr_cell_0_1892:
    movzx ecx, WORD PTR [r14+rbx*2+0]
__sbr_cell_0_1892_end:
__sbr_cell_0_1893:
    add r15, 320
__sbr_cell_0_1893_end:
__sbr_cell_0_1894:
    cmp r13, rcx
__sbr_cell_0_1894_end:
__sbr_cell_0_1895:
    jb ff_aac_sbr_apply.L8a50
__sbr_cell_0_1895_end:
__sbr_cell_0_1896:
    mov rax, QWORD PTR [rbp-88]
__sbr_cell_0_1896_end:
__sbr_cell_0_1897:
    movzx eax, WORD PTR [r14+rax*2+0]
__sbr_cell_0_1897_end:
__sbr_cell_0_1898:
    cmp ax, cx
__sbr_cell_0_1898_end:
__sbr_cell_0_1899:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_1899_end:
__sbr_cell_0_1900:
    mov rdi, QWORD PTR [rbp-120]
__sbr_cell_0_1900_end:
__sbr_cell_0_1901:
    mov r8, QWORD PTR [rbp-104]
__sbr_cell_0_1901_end:
__sbr_cell_0_1902:
    mov edx, DWORD PTR [rbp-80]
__sbr_cell_0_1902_end:
ff_aac_sbr_apply.L8a50_3:
__sbr_cell_0_1903:
    jae ff_aac_sbr_apply.L89e0
__sbr_cell_0_1903_end:
__sbr_cell_0_1904:
    mov rcx, rax
__sbr_cell_0_1904_end:
__sbr_cell_0_1905:
    sub rcx, QWORD PTR [rbp-96]
__sbr_cell_0_1905_end:
__sbr_cell_0_1906:
    cmp rcx, 47
__sbr_cell_0_1906_end:
__sbr_cell_0_1907:
    ja ff_aac_sbr_apply.L99f8
__sbr_cell_0_1907_end:
__sbr_cell_0_1908:
    vcvtsi2ss xmm0, xmm15, edx
__sbr_cell_0_1908_end:
__sbr_cell_0_1909:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_1909_end:
__sbr_cell_0_1910:
    inc rax
__sbr_cell_0_1910_end:
__sbr_cell_0_1911:
    .nops 1
__sbr_cell_0_1911_end:
ff_aac_sbr_apply.L8ad0:
__sbr_cell_0_1912:
    vmovss DWORD PTR [rdi+rcx*4+552416], xmm0
__sbr_cell_0_1912_end:
ff_aac_sbr_apply.L8ad0_1:
__sbr_cell_0_1913:
    movzx edx, WORD PTR [r14+rbx*2+0]
__sbr_cell_0_1913_end:
__sbr_cell_0_1914:
    cmp rax, rdx
__sbr_cell_0_1914_end:
__sbr_cell_0_1915:
    jae ff_aac_sbr_apply.L89e0
__sbr_cell_0_1915_end:
__sbr_cell_0_1916:
    inc rcx
__sbr_cell_0_1916_end:
__sbr_cell_0_1917:
    inc rax
__sbr_cell_0_1917_end:
__sbr_cell_0_1918:
    cmp rcx, 48
__sbr_cell_0_1918_end:
__sbr_cell_0_1919:
    jb ff_aac_sbr_apply.L8ad0
__sbr_cell_0_1919_end:
__sbr_cell_0_1920:
    jmp ff_aac_sbr_apply.L99f8
__sbr_cell_0_1920_end:
__sbr_cell_0_1921:
    .nops 1
__sbr_cell_0_1921_end:
ff_aac_sbr_apply.L8b00:
__sbr_cell_0_1922:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_1922_end:
__sbr_cell_0_1923:
    mov eax, DWORD PTR [rbx+8]
__sbr_cell_0_1923_end:
__sbr_cell_0_1924:
    cmp r8, rax
__sbr_cell_0_1924_end:
__sbr_cell_0_1925:
    jae ff_aac_sbr_apply.L9146
__sbr_cell_0_1925_end:
__sbr_cell_0_1926:
    lea rcx, [r8+1]
__sbr_cell_0_1926_end:
__sbr_cell_0_1927:
    add rdi, 192
__sbr_cell_0_1927_end:
__sbr_cell_0_1928:
    cmp r8, 8
__sbr_cell_0_1928_end:
__sbr_cell_0_1929:
    jne ff_aac_sbr_apply.L8970
__sbr_cell_0_1929_end:
__sbr_cell_0_1930:
    jmp ff_aac_sbr_apply.L9bff
__sbr_cell_0_1930_end:
ff_aac_sbr_apply.L8b2a:
__sbr_cell_0_1931:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_1931_end:
__sbr_cell_0_1932:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_0_1932_end:
__sbr_cell_0_1933:
    test eax, eax
__sbr_cell_0_1933_end:
__sbr_cell_0_1934:
    sete sil
__sbr_cell_0_1934_end:
__sbr_cell_0_1935:
    mov eax, ecx
__sbr_cell_0_1935_end:
__sbr_cell_0_1936:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_1936_end:
__sbr_cell_0_1937:
    mov rdi, QWORD PTR [rbp-80]
__sbr_cell_0_1937_end:
__sbr_cell_0_1938:
    cmp ecx, 2
__sbr_cell_0_1938_end:
__sbr_cell_0_1939:
    jae ff_aac_sbr_apply.L8b77
__sbr_cell_0_1939_end:
__sbr_cell_0_1940:
    jmp ff_aac_sbr_apply.L9146
__sbr_cell_0_1940_end:
ff_aac_sbr_apply.L8b4f:
__sbr_cell_0_1941:
    mov eax, DWORD PTR [r8+166264]
__sbr_cell_0_1941_end:
__sbr_cell_0_1942:
    add eax, DWORD PTR [r8+166272]
__sbr_cell_0_1942_end:
__sbr_cell_0_1943:
    sub eax, r12d
__sbr_cell_0_1943_end:
__sbr_cell_0_1944:
    ja ff_aac_sbr_apply.L7cbf
__sbr_cell_0_1944_end:
__sbr_cell_0_1945:
    jmp ff_aac_sbr_apply.L7ce4
__sbr_cell_0_1945_end:
ff_aac_sbr_apply.L8b6b:
__sbr_cell_0_1946:
    mov sil, 1
__sbr_cell_0_1946_end:
__sbr_cell_0_1947:
    cmp ecx, 2
__sbr_cell_0_1947_end:
__sbr_cell_0_1948:
    jb ff_aac_sbr_apply.L9146
__sbr_cell_0_1948_end:
ff_aac_sbr_apply.L8b77:
__sbr_cell_0_1949:
    movzx r12d, BYTE PTR [rbx+88733]
__sbr_cell_0_1949_end:
__sbr_cell_0_1950:
    cmp r12d, 18
__sbr_cell_0_1950_end:
__sbr_cell_0_1951:
    ja ff_aac_sbr_apply.L9146
__sbr_cell_0_1951_end:
__sbr_cell_0_1952:
    mov QWORD PTR [rbp-80], r14
__sbr_cell_0_1952_end:
__sbr_cell_0_1953:
    mov dl, 1
__sbr_cell_0_1953_end:
__sbr_cell_0_1954:
    test sil, sil
__sbr_cell_0_1954_end:
__sbr_cell_0_1955:
    jne ff_aac_sbr_apply.L8c4c
__sbr_cell_0_1955_end:
__sbr_cell_0_1956:
    movzx r15d, BYTE PTR [rbx+88734]
__sbr_cell_0_1956_end:
__sbr_cell_0_1957:
    sub r15d, r12d
__sbr_cell_0_1957_end:
__sbr_cell_0_1958:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_1958_end:
__sbr_cell_0_1959:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_1959_end:
__sbr_cell_0_1960:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_1960_end:
__sbr_cell_0_1961:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_1961_end:
__sbr_cell_0_1962:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_1962_end:
__sbr_cell_0_1963:
    add r15d, r15d
__sbr_cell_0_1963_end:
ff_aac_sbr_apply.L8b77_1:
__sbr_cell_0_1964:
    mov r14, rdi
__sbr_cell_0_1964_end:
__sbr_cell_0_1965:
    lea rdi, [rdi+rax*8+0]
__sbr_cell_0_1965_end:
__sbr_cell_0_1966:
    add rdi, 16
__sbr_cell_0_1966_end:
__sbr_cell_0_1967:
    mov esi, r15d
__sbr_cell_0_1967_end:
__sbr_cell_0_1968:
    mov r13, r8
__sbr_cell_0_1968_end:
__sbr_cell_0_1969:
    vzeroupper
__sbr_cell_0_1969_end:
__sbr_cell_0_1970:
    call QWORD PTR [r8+559880]
__sbr_cell_0_1970_end:
ff_aac_sbr_apply.L8b77_2:
__sbr_cell_0_1971:
    shl r12d, 4
__sbr_cell_0_1971_end:
__sbr_cell_0_1972:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_1972_end:
__sbr_cell_0_1973:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_0_1973_end:
__sbr_cell_0_1974:
    add rax, rcx
__sbr_cell_0_1974_end:
__sbr_cell_0_1975:
    add r12, rax
__sbr_cell_0_1975_end:
__sbr_cell_0_1976:
    xor ebx, ebx
__sbr_cell_0_1976_end:
__sbr_cell_0_1977:
    .nops 1
__sbr_cell_0_1977_end:
ff_aac_sbr_apply.L8bf0:
__sbr_cell_0_1978:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_1978_end:
__sbr_cell_0_1979:
    vmovss DWORD PTR [r13+rbx*4+552608], xmm0
__sbr_cell_0_1979_end:
__sbr_cell_0_1980:
    inc rbx
__sbr_cell_0_1980_end:
ff_aac_sbr_apply.L8bf0_1:
__sbr_cell_0_1981:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_1981_end:
__sbr_cell_0_1982:
    cmp rbx, rax
__sbr_cell_0_1982_end:
__sbr_cell_0_1983:
    mov r8, r13
__sbr_cell_0_1983_end:
__sbr_cell_0_1984:
    jae ff_aac_sbr_apply.L8c33
__sbr_cell_0_1984_end:
__sbr_cell_0_1985:
    mov rdi, r12
__sbr_cell_0_1985_end:
__sbr_cell_0_1986:
    mov esi, r15d
__sbr_cell_0_1986_end:
__sbr_cell_0_1987:
    mov r13, r8
__sbr_cell_0_1987_end:
__sbr_cell_0_1988:
    call QWORD PTR [r8+559880]
__sbr_cell_0_1988_end:
ff_aac_sbr_apply.L8bf0_2:
__sbr_cell_0_1989:
    add r12, 320
__sbr_cell_0_1989_end:
__sbr_cell_0_1990:
    cmp rbx, 48
__sbr_cell_0_1990_end:
__sbr_cell_0_1991:
    jne ff_aac_sbr_apply.L8bf0
__sbr_cell_0_1991_end:
__sbr_cell_0_1992:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_1992_end:
ff_aac_sbr_apply.L8c33:
__sbr_cell_0_1993:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_1993_end:
__sbr_cell_0_1994:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_0_1994_end:
__sbr_cell_0_1995:
    test eax, eax
__sbr_cell_0_1995_end:
__sbr_cell_0_1996:
    sete dl
__sbr_cell_0_1996_end:
__sbr_cell_0_1997:
    mov eax, ecx
__sbr_cell_0_1997_end:
__sbr_cell_0_1998:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_1998_end:
__sbr_cell_0_1999:
    mov rdi, r14
__sbr_cell_0_1999_end:
ff_aac_sbr_apply.L8c4c:
__sbr_cell_0_2000:
    cmp ecx, 3
__sbr_cell_0_2000_end:
__sbr_cell_0_2001:
    jb ff_aac_sbr_apply.L9146
__sbr_cell_0_2001_end:
__sbr_cell_0_2002:
    movzx r12d, BYTE PTR [rbx+88734]
__sbr_cell_0_2002_end:
__sbr_cell_0_2003:
    cmp r12d, 18
__sbr_cell_0_2003_end:
__sbr_cell_0_2004:
    ja ff_aac_sbr_apply.L9146
__sbr_cell_0_2004_end:
__sbr_cell_0_2005:
    mov sil, 1
__sbr_cell_0_2005_end:
__sbr_cell_0_2006:
    test dl, dl
__sbr_cell_0_2006_end:
__sbr_cell_0_2007:
    jne ff_aac_sbr_apply.L8d26
__sbr_cell_0_2007_end:
__sbr_cell_0_2008:
    movzx r15d, BYTE PTR [rbx+88735]
__sbr_cell_0_2008_end:
__sbr_cell_0_2009:
    sub r15d, r12d
__sbr_cell_0_2009_end:
__sbr_cell_0_2010:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_2010_end:
__sbr_cell_0_2011:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_2011_end:
__sbr_cell_0_2012:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_2012_end:
__sbr_cell_0_2013:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_2013_end:
__sbr_cell_0_2014:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_2014_end:
ff_aac_sbr_apply.L8c4c_1:
__sbr_cell_0_2015:
    add r15d, r15d
__sbr_cell_0_2015_end:
__sbr_cell_0_2016:
    mov r14, rdi
__sbr_cell_0_2016_end:
__sbr_cell_0_2017:
    lea rdi, [rdi+rax*8+0]
__sbr_cell_0_2017_end:
__sbr_cell_0_2018:
    add rdi, 16
__sbr_cell_0_2018_end:
__sbr_cell_0_2019:
    mov esi, r15d
__sbr_cell_0_2019_end:
__sbr_cell_0_2020:
    mov r13, r8
__sbr_cell_0_2020_end:
__sbr_cell_0_2021:
    vzeroupper
__sbr_cell_0_2021_end:
__sbr_cell_0_2022:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2022_end:
ff_aac_sbr_apply.L8c4c_2:
__sbr_cell_0_2023:
    shl r12d, 4
__sbr_cell_0_2023_end:
__sbr_cell_0_2024:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_2024_end:
__sbr_cell_0_2025:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_0_2025_end:
__sbr_cell_0_2026:
    add rax, rcx
__sbr_cell_0_2026_end:
__sbr_cell_0_2027:
    add r12, rax
__sbr_cell_0_2027_end:
__sbr_cell_0_2028:
    xor ebx, ebx
__sbr_cell_0_2028_end:
ff_aac_sbr_apply.L8cc9:
__sbr_cell_0_2029:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_2029_end:
__sbr_cell_0_2030:
    vmovss DWORD PTR [r13+rbx*4+552800], xmm0
__sbr_cell_0_2030_end:
__sbr_cell_0_2031:
    inc rbx
__sbr_cell_0_2031_end:
ff_aac_sbr_apply.L8cc9_1:
__sbr_cell_0_2032:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_2032_end:
__sbr_cell_0_2033:
    cmp rbx, rax
__sbr_cell_0_2033_end:
__sbr_cell_0_2034:
    mov r8, r13
__sbr_cell_0_2034_end:
__sbr_cell_0_2035:
    jae ff_aac_sbr_apply.L8d0c
__sbr_cell_0_2035_end:
__sbr_cell_0_2036:
    mov rdi, r12
__sbr_cell_0_2036_end:
__sbr_cell_0_2037:
    mov esi, r15d
__sbr_cell_0_2037_end:
__sbr_cell_0_2038:
    mov r13, r8
__sbr_cell_0_2038_end:
__sbr_cell_0_2039:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2039_end:
ff_aac_sbr_apply.L8cc9_2:
__sbr_cell_0_2040:
    add r12, 320
__sbr_cell_0_2040_end:
__sbr_cell_0_2041:
    cmp rbx, 48
__sbr_cell_0_2041_end:
__sbr_cell_0_2042:
    jne ff_aac_sbr_apply.L8cc9
__sbr_cell_0_2042_end:
__sbr_cell_0_2043:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_2043_end:
ff_aac_sbr_apply.L8d0c:
__sbr_cell_0_2044:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2044_end:
__sbr_cell_0_2045:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_0_2045_end:
__sbr_cell_0_2046:
    test eax, eax
__sbr_cell_0_2046_end:
__sbr_cell_0_2047:
    sete sil
__sbr_cell_0_2047_end:
__sbr_cell_0_2048:
    mov eax, ecx
__sbr_cell_0_2048_end:
__sbr_cell_0_2049:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2049_end:
__sbr_cell_0_2050:
    mov rdi, r14
__sbr_cell_0_2050_end:
ff_aac_sbr_apply.L8d26:
__sbr_cell_0_2051:
    cmp ecx, 4
__sbr_cell_0_2051_end:
__sbr_cell_0_2052:
    jb ff_aac_sbr_apply.L9146
__sbr_cell_0_2052_end:
__sbr_cell_0_2053:
    movzx r12d, BYTE PTR [rbx+88735]
__sbr_cell_0_2053_end:
__sbr_cell_0_2054:
    cmp r12d, 18
__sbr_cell_0_2054_end:
__sbr_cell_0_2055:
    ja ff_aac_sbr_apply.L9146
__sbr_cell_0_2055_end:
__sbr_cell_0_2056:
    mov dl, 1
__sbr_cell_0_2056_end:
__sbr_cell_0_2057:
    test sil, sil
__sbr_cell_0_2057_end:
__sbr_cell_0_2058:
    jne ff_aac_sbr_apply.L8dff
__sbr_cell_0_2058_end:
__sbr_cell_0_2059:
    movzx r15d, BYTE PTR [rbx+88736]
__sbr_cell_0_2059_end:
__sbr_cell_0_2060:
    sub r15d, r12d
__sbr_cell_0_2060_end:
__sbr_cell_0_2061:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_2061_end:
__sbr_cell_0_2062:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_2062_end:
__sbr_cell_0_2063:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_2063_end:
__sbr_cell_0_2064:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_2064_end:
__sbr_cell_0_2065:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_2065_end:
ff_aac_sbr_apply.L8d26_1:
__sbr_cell_0_2066:
    add r15d, r15d
__sbr_cell_0_2066_end:
__sbr_cell_0_2067:
    mov r14, rdi
__sbr_cell_0_2067_end:
__sbr_cell_0_2068:
    lea rdi, [rdi+rax*8+0]
__sbr_cell_0_2068_end:
__sbr_cell_0_2069:
    add rdi, 16
__sbr_cell_0_2069_end:
__sbr_cell_0_2070:
    mov esi, r15d
__sbr_cell_0_2070_end:
__sbr_cell_0_2071:
    mov r13, r8
__sbr_cell_0_2071_end:
__sbr_cell_0_2072:
    vzeroupper
__sbr_cell_0_2072_end:
__sbr_cell_0_2073:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2073_end:
ff_aac_sbr_apply.L8d26_2:
__sbr_cell_0_2074:
    shl r12d, 4
__sbr_cell_0_2074_end:
__sbr_cell_0_2075:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_2075_end:
__sbr_cell_0_2076:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_0_2076_end:
__sbr_cell_0_2077:
    add rax, rcx
__sbr_cell_0_2077_end:
__sbr_cell_0_2078:
    add r12, rax
__sbr_cell_0_2078_end:
__sbr_cell_0_2079:
    xor ebx, ebx
__sbr_cell_0_2079_end:
ff_aac_sbr_apply.L8da3:
__sbr_cell_0_2080:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_2080_end:
__sbr_cell_0_2081:
    vmovss DWORD PTR [r13+rbx*4+552992], xmm0
__sbr_cell_0_2081_end:
__sbr_cell_0_2082:
    inc rbx
__sbr_cell_0_2082_end:
ff_aac_sbr_apply.L8da3_1:
__sbr_cell_0_2083:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_2083_end:
__sbr_cell_0_2084:
    cmp rbx, rax
__sbr_cell_0_2084_end:
__sbr_cell_0_2085:
    mov r8, r13
__sbr_cell_0_2085_end:
__sbr_cell_0_2086:
    jae ff_aac_sbr_apply.L8de6
__sbr_cell_0_2086_end:
__sbr_cell_0_2087:
    mov rdi, r12
__sbr_cell_0_2087_end:
__sbr_cell_0_2088:
    mov esi, r15d
__sbr_cell_0_2088_end:
__sbr_cell_0_2089:
    mov r13, r8
__sbr_cell_0_2089_end:
__sbr_cell_0_2090:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2090_end:
ff_aac_sbr_apply.L8da3_2:
__sbr_cell_0_2091:
    add r12, 320
__sbr_cell_0_2091_end:
__sbr_cell_0_2092:
    cmp rbx, 48
__sbr_cell_0_2092_end:
__sbr_cell_0_2093:
    jne ff_aac_sbr_apply.L8da3
__sbr_cell_0_2093_end:
__sbr_cell_0_2094:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_2094_end:
ff_aac_sbr_apply.L8de6:
__sbr_cell_0_2095:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2095_end:
__sbr_cell_0_2096:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_0_2096_end:
__sbr_cell_0_2097:
    test eax, eax
__sbr_cell_0_2097_end:
__sbr_cell_0_2098:
    sete dl
__sbr_cell_0_2098_end:
__sbr_cell_0_2099:
    mov eax, ecx
__sbr_cell_0_2099_end:
__sbr_cell_0_2100:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2100_end:
__sbr_cell_0_2101:
    mov rdi, r14
__sbr_cell_0_2101_end:
ff_aac_sbr_apply.L8dff:
__sbr_cell_0_2102:
    cmp ecx, 5
__sbr_cell_0_2102_end:
__sbr_cell_0_2103:
    jb ff_aac_sbr_apply.L9146
__sbr_cell_0_2103_end:
__sbr_cell_0_2104:
    movzx r12d, BYTE PTR [rbx+88736]
__sbr_cell_0_2104_end:
__sbr_cell_0_2105:
    cmp r12d, 18
__sbr_cell_0_2105_end:
__sbr_cell_0_2106:
    ja ff_aac_sbr_apply.L9146
__sbr_cell_0_2106_end:
__sbr_cell_0_2107:
    mov sil, 1
__sbr_cell_0_2107_end:
__sbr_cell_0_2108:
    test dl, dl
__sbr_cell_0_2108_end:
__sbr_cell_0_2109:
    jne ff_aac_sbr_apply.L8ed9
__sbr_cell_0_2109_end:
__sbr_cell_0_2110:
    movzx r15d, BYTE PTR [rbx+88737]
__sbr_cell_0_2110_end:
__sbr_cell_0_2111:
    sub r15d, r12d
__sbr_cell_0_2111_end:
__sbr_cell_0_2112:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_2112_end:
__sbr_cell_0_2113:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_2113_end:
__sbr_cell_0_2114:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_2114_end:
__sbr_cell_0_2115:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_2115_end:
__sbr_cell_0_2116:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_2116_end:
ff_aac_sbr_apply.L8dff_1:
__sbr_cell_0_2117:
    add r15d, r15d
__sbr_cell_0_2117_end:
__sbr_cell_0_2118:
    mov r14, rdi
__sbr_cell_0_2118_end:
__sbr_cell_0_2119:
    lea rdi, [rdi+rax*8+0]
__sbr_cell_0_2119_end:
__sbr_cell_0_2120:
    add rdi, 16
__sbr_cell_0_2120_end:
__sbr_cell_0_2121:
    mov esi, r15d
__sbr_cell_0_2121_end:
__sbr_cell_0_2122:
    mov r13, r8
__sbr_cell_0_2122_end:
__sbr_cell_0_2123:
    vzeroupper
__sbr_cell_0_2123_end:
__sbr_cell_0_2124:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2124_end:
ff_aac_sbr_apply.L8dff_2:
__sbr_cell_0_2125:
    shl r12d, 4
__sbr_cell_0_2125_end:
__sbr_cell_0_2126:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_2126_end:
__sbr_cell_0_2127:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_0_2127_end:
__sbr_cell_0_2128:
    add rax, rcx
__sbr_cell_0_2128_end:
__sbr_cell_0_2129:
    add r12, rax
__sbr_cell_0_2129_end:
__sbr_cell_0_2130:
    xor ebx, ebx
__sbr_cell_0_2130_end:
ff_aac_sbr_apply.L8e7c:
__sbr_cell_0_2131:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_2131_end:
__sbr_cell_0_2132:
    vmovss DWORD PTR [r13+rbx*4+553184], xmm0
__sbr_cell_0_2132_end:
__sbr_cell_0_2133:
    inc rbx
__sbr_cell_0_2133_end:
ff_aac_sbr_apply.L8e7c_1:
__sbr_cell_0_2134:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_2134_end:
__sbr_cell_0_2135:
    cmp rbx, rax
__sbr_cell_0_2135_end:
__sbr_cell_0_2136:
    mov r8, r13
__sbr_cell_0_2136_end:
__sbr_cell_0_2137:
    jae ff_aac_sbr_apply.L8ebf
__sbr_cell_0_2137_end:
__sbr_cell_0_2138:
    mov rdi, r12
__sbr_cell_0_2138_end:
__sbr_cell_0_2139:
    mov esi, r15d
__sbr_cell_0_2139_end:
__sbr_cell_0_2140:
    mov r13, r8
__sbr_cell_0_2140_end:
__sbr_cell_0_2141:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2141_end:
ff_aac_sbr_apply.L8e7c_2:
__sbr_cell_0_2142:
    add r12, 320
__sbr_cell_0_2142_end:
__sbr_cell_0_2143:
    cmp rbx, 48
__sbr_cell_0_2143_end:
__sbr_cell_0_2144:
    jne ff_aac_sbr_apply.L8e7c
__sbr_cell_0_2144_end:
__sbr_cell_0_2145:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_2145_end:
ff_aac_sbr_apply.L8ebf:
__sbr_cell_0_2146:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2146_end:
__sbr_cell_0_2147:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_0_2147_end:
__sbr_cell_0_2148:
    test eax, eax
__sbr_cell_0_2148_end:
__sbr_cell_0_2149:
    sete sil
__sbr_cell_0_2149_end:
__sbr_cell_0_2150:
    mov eax, ecx
__sbr_cell_0_2150_end:
__sbr_cell_0_2151:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2151_end:
__sbr_cell_0_2152:
    mov rdi, r14
__sbr_cell_0_2152_end:
ff_aac_sbr_apply.L8ed9:
__sbr_cell_0_2153:
    cmp ecx, 6
__sbr_cell_0_2153_end:
__sbr_cell_0_2154:
    jb ff_aac_sbr_apply.L9146
__sbr_cell_0_2154_end:
__sbr_cell_0_2155:
    movzx r12d, BYTE PTR [rbx+88737]
__sbr_cell_0_2155_end:
__sbr_cell_0_2156:
    cmp r12d, 18
__sbr_cell_0_2156_end:
__sbr_cell_0_2157:
    ja ff_aac_sbr_apply.L9146
__sbr_cell_0_2157_end:
__sbr_cell_0_2158:
    mov dl, 1
__sbr_cell_0_2158_end:
__sbr_cell_0_2159:
    test sil, sil
__sbr_cell_0_2159_end:
__sbr_cell_0_2160:
    jne ff_aac_sbr_apply.L8fa4
__sbr_cell_0_2160_end:
__sbr_cell_0_2161:
    movzx r15d, BYTE PTR [rbx+88738]
__sbr_cell_0_2161_end:
__sbr_cell_0_2162:
    sub r15d, r12d
__sbr_cell_0_2162_end:
__sbr_cell_0_2163:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_2163_end:
__sbr_cell_0_2164:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_2164_end:
__sbr_cell_0_2165:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_2165_end:
__sbr_cell_0_2166:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_2166_end:
__sbr_cell_0_2167:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_2167_end:
ff_aac_sbr_apply.L8ed9_1:
__sbr_cell_0_2168:
    add r15d, r15d
__sbr_cell_0_2168_end:
__sbr_cell_0_2169:
    mov r14, rdi
__sbr_cell_0_2169_end:
__sbr_cell_0_2170:
    lea rdi, [rdi+rax*8+0]
__sbr_cell_0_2170_end:
__sbr_cell_0_2171:
    add rdi, 16
__sbr_cell_0_2171_end:
__sbr_cell_0_2172:
    mov esi, r15d
__sbr_cell_0_2172_end:
__sbr_cell_0_2173:
    mov r13, r8
__sbr_cell_0_2173_end:
__sbr_cell_0_2174:
    vzeroupper
__sbr_cell_0_2174_end:
__sbr_cell_0_2175:
    call QWORD PTR [r8+559880]
__sbr_cell_0_2175_end:
ff_aac_sbr_apply.L8ed9_2:
__sbr_cell_0_2176:
    shl r12d, 4
__sbr_cell_0_2176_end:
__sbr_cell_0_2177:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_2177_end:
__sbr_cell_0_2178:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_0_2178_end:
__sbr_cell_0_2179:
    add rax, rcx
__sbr_cell_0_2179_end:
__sbr_cell_0_2180:
    add r12, rax
__sbr_cell_0_2180_end:
__sbr_cell_0_2181:
    xor ebx, ebx
__sbr_cell_0_2181_end:
ff_aac_sbr_apply.L8f56:
__sbr_cell_0_2182:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_2182_end:
__sbr_cell_0_2183:
    vmovss DWORD PTR [r13+rbx*4+553376], xmm0
__sbr_cell_0_2183_end:
__sbr_cell_0_2184:
    inc rbx
__sbr_cell_0_2184_end:
ff_aac_sbr_apply.L8f56_1:
__sbr_cell_0_2185:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_2185_end:
__sbr_cell_0_2186:
    cmp rbx, rax
__sbr_cell_0_2186_end:
__sbr_cell_0_2187:
    jae ff_aac_sbr_apply.L8f93
__sbr_cell_0_2187_end:
__sbr_cell_0_2188:
    mov rdi, r12
__sbr_cell_0_2188_end:
__sbr_cell_0_2189:
    mov esi, r15d
__sbr_cell_0_2189_end:
__sbr_cell_0_2190:
    call QWORD PTR [r13+559880]
__sbr_cell_0_2190_end:
ff_aac_sbr_apply.L8f56_2:
__sbr_cell_0_2191:
    add r12, 320
__sbr_cell_0_2191_end:
__sbr_cell_0_2192:
    cmp rbx, 48
__sbr_cell_0_2192_end:
__sbr_cell_0_2193:
    jne ff_aac_sbr_apply.L8f56
__sbr_cell_0_2193_end:
__sbr_cell_0_2194:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_2194_end:
ff_aac_sbr_apply.L8f93:
__sbr_cell_0_2195:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2195_end:
__sbr_cell_0_2196:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_0_2196_end:
__sbr_cell_0_2197:
    test eax, eax
__sbr_cell_0_2197_end:
__sbr_cell_0_2198:
    sete dl
__sbr_cell_0_2198_end:
__sbr_cell_0_2199:
    mov eax, ecx
__sbr_cell_0_2199_end:
__sbr_cell_0_2200:
    mov rdi, r14
__sbr_cell_0_2200_end:
ff_aac_sbr_apply.L8fa4:
__sbr_cell_0_2201:
    cmp ecx, 7
__sbr_cell_0_2201_end:
__sbr_cell_0_2202:
    jb ff_aac_sbr_apply.L9063
__sbr_cell_0_2202_end:
__sbr_cell_0_2203:
    movzx r12d, BYTE PTR [rbx+88738]
__sbr_cell_0_2203_end:
__sbr_cell_0_2204:
    cmp r12d, 18
__sbr_cell_0_2204_end:
__sbr_cell_0_2205:
    ja ff_aac_sbr_apply.L913a
__sbr_cell_0_2205_end:
__sbr_cell_0_2206:
    mov r14, rdi
__sbr_cell_0_2206_end:
__sbr_cell_0_2207:
    mov sil, 1
__sbr_cell_0_2207_end:
__sbr_cell_0_2208:
    test dl, dl
__sbr_cell_0_2208_end:
__sbr_cell_0_2209:
    jne ff_aac_sbr_apply.L907f
__sbr_cell_0_2209_end:
__sbr_cell_0_2210:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_0_2210_end:
__sbr_cell_0_2211:
    movzx r15d, BYTE PTR [rax+88739]
__sbr_cell_0_2211_end:
__sbr_cell_0_2212:
    sub r15d, r12d
__sbr_cell_0_2212_end:
__sbr_cell_0_2213:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_2213_end:
__sbr_cell_0_2214:
    lea eax, [r12+r12*1+0]
__sbr_cell_0_2214_end:
__sbr_cell_0_2215:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_2215_end:
ff_aac_sbr_apply.L8fa4_1:
__sbr_cell_0_2216:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_2216_end:
__sbr_cell_0_2217:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_2217_end:
ff_aac_sbr_apply.L8fa4_2:
__sbr_cell_0_2218:
    add r15d, r15d
__sbr_cell_0_2218_end:
__sbr_cell_0_2219:
    lea rdi, [r14+rax*8+0]
__sbr_cell_0_2219_end:
__sbr_cell_0_2220:
    add rdi, 16
__sbr_cell_0_2220_end:
__sbr_cell_0_2221:
    mov esi, r15d
__sbr_cell_0_2221_end:
__sbr_cell_0_2222:
    mov r13, QWORD PTR [rbp-56]
__sbr_cell_0_2222_end:
__sbr_cell_0_2223:
    vzeroupper
__sbr_cell_0_2223_end:
__sbr_cell_0_2224:
    call QWORD PTR [r13+559880]
__sbr_cell_0_2224_end:
ff_aac_sbr_apply.L8fa4_3:
__sbr_cell_0_2225:
    shl r12d, 4
__sbr_cell_0_2225_end:
__sbr_cell_0_2226:
    mov rax, QWORD PTR [rbp-112]
__sbr_cell_0_2226_end:
__sbr_cell_0_2227:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_0_2227_end:
__sbr_cell_0_2228:
    add rax, rcx
__sbr_cell_0_2228_end:
__sbr_cell_0_2229:
    add r12, rax
__sbr_cell_0_2229_end:
__sbr_cell_0_2230:
    xor ebx, ebx
__sbr_cell_0_2230_end:
ff_aac_sbr_apply.L9026:
__sbr_cell_0_2231:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_2231_end:
__sbr_cell_0_2232:
    vmovss DWORD PTR [r13+rbx*4+553568], xmm0
__sbr_cell_0_2232_end:
__sbr_cell_0_2233:
    inc rbx
__sbr_cell_0_2233_end:
ff_aac_sbr_apply.L9026_1:
__sbr_cell_0_2234:
    mov eax, DWORD PTR [r13+166272]
__sbr_cell_0_2234_end:
__sbr_cell_0_2235:
    cmp rbx, rax
__sbr_cell_0_2235_end:
__sbr_cell_0_2236:
    jae ff_aac_sbr_apply.L9070
__sbr_cell_0_2236_end:
__sbr_cell_0_2237:
    mov rdi, r12
__sbr_cell_0_2237_end:
__sbr_cell_0_2238:
    mov esi, r15d
__sbr_cell_0_2238_end:
__sbr_cell_0_2239:
    call QWORD PTR [r13+559880]
__sbr_cell_0_2239_end:
ff_aac_sbr_apply.L9026_2:
__sbr_cell_0_2240:
    add r12, 320
__sbr_cell_0_2240_end:
__sbr_cell_0_2241:
    cmp rbx, 48
__sbr_cell_0_2241_end:
__sbr_cell_0_2242:
    jne ff_aac_sbr_apply.L9026
__sbr_cell_0_2242_end:
__sbr_cell_0_2243:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_2243_end:
ff_aac_sbr_apply.L9063:
__sbr_cell_0_2244:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2244_end:
__sbr_cell_0_2245:
    jmp ff_aac_sbr_apply.L9146
__sbr_cell_0_2245_end:
ff_aac_sbr_apply.L9070:
__sbr_cell_0_2246:
    mov rcx, QWORD PTR [rbp-72]
__sbr_cell_0_2246_end:
__sbr_cell_0_2247:
    mov ecx, DWORD PTR [rcx+8]
__sbr_cell_0_2247_end:
__sbr_cell_0_2248:
    test eax, eax
__sbr_cell_0_2248_end:
__sbr_cell_0_2249:
    sete sil
__sbr_cell_0_2249_end:
__sbr_cell_0_2250:
    mov eax, ecx
__sbr_cell_0_2250_end:
ff_aac_sbr_apply.L907f:
__sbr_cell_0_2251:
    cmp ecx, 8
__sbr_cell_0_2251_end:
__sbr_cell_0_2252:
    jb ff_aac_sbr_apply.L913a
__sbr_cell_0_2252_end:
__sbr_cell_0_2253:
    mov rdx, QWORD PTR [rbp-72]
__sbr_cell_0_2253_end:
__sbr_cell_0_2254:
    movzx ebx, BYTE PTR [rdx+88739]
__sbr_cell_0_2254_end:
__sbr_cell_0_2255:
    cmp ebx, 18
__sbr_cell_0_2255_end:
__sbr_cell_0_2256:
    ja ff_aac_sbr_apply.L913a
__sbr_cell_0_2256_end:
__sbr_cell_0_2257:
    test sil, sil
__sbr_cell_0_2257_end:
__sbr_cell_0_2258:
    jne ff_aac_sbr_apply.L99cf
__sbr_cell_0_2258_end:
__sbr_cell_0_2259:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_0_2259_end:
__sbr_cell_0_2260:
    movzx r15d, BYTE PTR [rax+88740]
__sbr_cell_0_2260_end:
__sbr_cell_0_2261:
    sub r15d, ebx
__sbr_cell_0_2261_end:
__sbr_cell_0_2262:
    vcvtsi2ss xmm0, xmm15, r15d
__sbr_cell_0_2262_end:
__sbr_cell_0_2263:
    lea eax, [rbx+rbx*1+0]
__sbr_cell_0_2263_end:
__sbr_cell_0_2264:
    vmovss xmm1, DWORD PTR [rip+LCPI14_12]
__sbr_cell_0_2264_end:
__sbr_cell_0_2265:
    vdivss xmm0, xmm1, xmm0
__sbr_cell_0_2265_end:
ff_aac_sbr_apply.L907f_1:
__sbr_cell_0_2266:
    vmovss DWORD PTR [rbp-48], xmm0
__sbr_cell_0_2266_end:
ff_aac_sbr_apply.L907f_2:
__sbr_cell_0_2267:
    add r15d, r15d
__sbr_cell_0_2267_end:
__sbr_cell_0_2268:
    lea rdi, [r14+rax*8+0]
__sbr_cell_0_2268_end:
__sbr_cell_0_2269:
    add rdi, 16
__sbr_cell_0_2269_end:
__sbr_cell_0_2270:
    mov esi, r15d
__sbr_cell_0_2270_end:
__sbr_cell_0_2271:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_0_2271_end:
__sbr_cell_0_2272:
    vzeroupper
__sbr_cell_0_2272_end:
__sbr_cell_0_2273:
    call QWORD PTR [r14+559880]
__sbr_cell_0_2273_end:
ff_aac_sbr_apply.L907f_3:
__sbr_cell_0_2274:
    shl ebx, 4
__sbr_cell_0_2274_end:
__sbr_cell_0_2275:
    mov r12, QWORD PTR [rbp-80]
__sbr_cell_0_2275_end:
__sbr_cell_0_2276:
    add r12, QWORD PTR [rbp-112]
__sbr_cell_0_2276_end:
__sbr_cell_0_2277:
    add r12, rbx
__sbr_cell_0_2277_end:
__sbr_cell_0_2278:
    xor ebx, ebx
__sbr_cell_0_2278_end:
ff_aac_sbr_apply.L90f9:
__sbr_cell_0_2279:
    vmulss xmm0, xmm0, DWORD PTR [rbp-48]
__sbr_cell_0_2279_end:
__sbr_cell_0_2280:
    vmovss DWORD PTR [r14+rbx*4+553760], xmm0
__sbr_cell_0_2280_end:
__sbr_cell_0_2281:
    inc rbx
__sbr_cell_0_2281_end:
ff_aac_sbr_apply.L90f9_1:
__sbr_cell_0_2282:
    mov eax, DWORD PTR [r14+166272]
__sbr_cell_0_2282_end:
__sbr_cell_0_2283:
    cmp rbx, rax
__sbr_cell_0_2283_end:
__sbr_cell_0_2284:
    jae ff_aac_sbr_apply.L99c6
__sbr_cell_0_2284_end:
__sbr_cell_0_2285:
    mov rdi, r12
__sbr_cell_0_2285_end:
__sbr_cell_0_2286:
    mov esi, r15d
__sbr_cell_0_2286_end:
__sbr_cell_0_2287:
    call QWORD PTR [r14+559880]
__sbr_cell_0_2287_end:
ff_aac_sbr_apply.L90f9_2:
__sbr_cell_0_2288:
    add r12, 320
__sbr_cell_0_2288_end:
__sbr_cell_0_2289:
    cmp rbx, 48
__sbr_cell_0_2289_end:
__sbr_cell_0_2290:
    jne ff_aac_sbr_apply.L90f9
__sbr_cell_0_2290_end:
__sbr_cell_0_2291:
    jmp ff_aac_sbr_apply.L9b95
__sbr_cell_0_2291_end:
ff_aac_sbr_apply.L913a:
__sbr_cell_0_2292:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2292_end:
__sbr_cell_0_2293:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2293_end:
ff_aac_sbr_apply.L9146:
__sbr_cell_0_2294:
    test eax, eax
__sbr_cell_0_2294_end:
__sbr_cell_0_2295:
    je ff_aac_sbr_apply.L98e0
__sbr_cell_0_2295_end:
ff_aac_sbr_apply.L914e:
__sbr_cell_0_2296:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_2296_end:
__sbr_cell_0_2297:
    mov eax, DWORD PTR [rax+477964]
__sbr_cell_0_2297_end:
__sbr_cell_0_2298:
    mov QWORD PTR [rbp-120], rax
__sbr_cell_0_2298_end:
__sbr_cell_0_2299:
    test rax, rax
__sbr_cell_0_2299_end:
__sbr_cell_0_2300:
    je ff_aac_sbr_apply.L98e0
__sbr_cell_0_2300_end:
ff_aac_sbr_apply.L914e_1:
__sbr_cell_0_2301:
    mov r10, QWORD PTR [rbp-56]
__sbr_cell_0_2301_end:
__sbr_cell_0_2302:
    mov ecx, DWORD PTR [r10+166264]
__sbr_cell_0_2302_end:
__sbr_cell_0_2303:
    movzx eax, WORD PTR [r10+478226]
__sbr_cell_0_2303_end:
__sbr_cell_0_2304:
    mov WORD PTR [rbp-130], ax
__sbr_cell_0_2304_end:
ff_aac_sbr_apply.L914e_2:
__sbr_cell_0_2305:
    mov rax, QWORD PTR [rbp-152]
__sbr_cell_0_2305_end:
__sbr_cell_0_2306:
    add rax, QWORD PTR [rbp-352]
__sbr_cell_0_2306_end:
__sbr_cell_0_2307:
    mov QWORD PTR [rbp-152], rax
__sbr_cell_0_2307_end:
__sbr_cell_0_2308:
    mov eax, ecx
__sbr_cell_0_2308_end:
__sbr_cell_0_2309:
    neg eax
__sbr_cell_0_2309_end:
__sbr_cell_0_2310:
    mov DWORD PTR [rbp-244], eax
__sbr_cell_0_2310_end:
ff_aac_sbr_apply.L914e_3:
__sbr_cell_0_2311:
    mov rdi, QWORD PTR [rbp-344]
__sbr_cell_0_2311_end:
__sbr_cell_0_2312:
    mov r8, QWORD PTR [rbp-264]
__sbr_cell_0_2312_end:
__sbr_cell_0_2313:
    mov r9, QWORD PTR [rbp-208]
__sbr_cell_0_2313_end:
__sbr_cell_0_2314:
    mov r11, QWORD PTR [rbp-256]
__sbr_cell_0_2314_end:
__sbr_cell_0_2315:
    xor r12d, r12d
__sbr_cell_0_2315_end:
__sbr_cell_0_2316:
    jmp ff_aac_sbr_apply.L91f7
__sbr_cell_0_2316_end:
__sbr_cell_0_2317:
    .nops 1
__sbr_cell_0_2317_end:
ff_aac_sbr_apply.L91c0:
__sbr_cell_0_2318:
    inc r12
__sbr_cell_0_2318_end:
__sbr_cell_0_2319:
    mov eax, DWORD PTR [rbx+8]
__sbr_cell_0_2319_end:
__sbr_cell_0_2320:
    add QWORD PTR [rbp-152], 48
__sbr_cell_0_2320_end:
__sbr_cell_0_2321:
    add r11, 192
__sbr_cell_0_2321_end:
__sbr_cell_0_2322:
    add r10, 48
__sbr_cell_0_2322_end:
__sbr_cell_0_2323:
    add r9, 192
__sbr_cell_0_2323_end:
__sbr_cell_0_2324:
    add r8, 192
__sbr_cell_0_2324_end:
__sbr_cell_0_2325:
    add rdi, 192
__sbr_cell_0_2325_end:
__sbr_cell_0_2326:
    cmp r12, rax
__sbr_cell_0_2326_end:
__sbr_cell_0_2327:
    jae ff_aac_sbr_apply.L98e0
__sbr_cell_0_2327_end:
ff_aac_sbr_apply.L91f7:
__sbr_cell_0_2328:
    mov eax, DWORD PTR [rbx+14600]
__sbr_cell_0_2328_end:
__sbr_cell_0_2329:
    cmp r12, rax
__sbr_cell_0_2329_end:
__sbr_cell_0_2330:
    jne ff_aac_sbr_apply.L9206
__sbr_cell_0_2330_end:
__sbr_cell_0_2331:
    xor edx, edx
__sbr_cell_0_2331_end:
__sbr_cell_0_2332:
    jmp ff_aac_sbr_apply.L9215
__sbr_cell_0_2332_end:
ff_aac_sbr_apply.L9206:
__sbr_cell_0_2333:
    mov rax, QWORD PTR [rbp-272]
__sbr_cell_0_2333_end:
__sbr_cell_0_2334:
    mov eax, DWORD PTR [rax+0]
__sbr_cell_0_2334_end:
__sbr_cell_0_2335:
    cmp r12, rax
__sbr_cell_0_2335_end:
__sbr_cell_0_2336:
    setne dl
__sbr_cell_0_2336_end:
ff_aac_sbr_apply.L9215:
__sbr_cell_0_2337:
    mov rax, r12
__sbr_cell_0_2337_end:
__sbr_cell_0_2338:
    shl rax, 6
__sbr_cell_0_2338_end:
__sbr_cell_0_2339:
    lea rsi, [rax+rax*2+0]
__sbr_cell_0_2339_end:
__sbr_cell_0_2340:
    mov rax, QWORD PTR [rbp-208]
__sbr_cell_0_2340_end:
__sbr_cell_0_2341:
    add rax, rsi
__sbr_cell_0_2341_end:
__sbr_cell_0_2342:
    mov QWORD PTR [rbp-96], rax
__sbr_cell_0_2342_end:
ff_aac_sbr_apply.L9215_1:
__sbr_cell_0_2343:
    mov rax, QWORD PTR [rbp-264]
__sbr_cell_0_2343_end:
__sbr_cell_0_2344:
    add rax, rsi
__sbr_cell_0_2344_end:
__sbr_cell_0_2345:
    mov QWORD PTR [rbp-232], rax
__sbr_cell_0_2345_end:
ff_aac_sbr_apply.L9215_2:
__sbr_cell_0_2346:
    mov rax, QWORD PTR [rbp-368]
__sbr_cell_0_2346_end:
__sbr_cell_0_2347:
    add rax, rsi
__sbr_cell_0_2347_end:
__sbr_cell_0_2348:
    mov QWORD PTR [rbp-224], rax
__sbr_cell_0_2348_end:
ff_aac_sbr_apply.L9215_3:
__sbr_cell_0_2349:
    mov rax, QWORD PTR [rbp-376]
__sbr_cell_0_2349_end:
__sbr_cell_0_2350:
    add rax, rsi
__sbr_cell_0_2350_end:
__sbr_cell_0_2351:
    mov QWORD PTR [rbp-216], rax
__sbr_cell_0_2351_end:
ff_aac_sbr_apply.L9215_4:
__sbr_cell_0_2352:
    add rsi, QWORD PTR [rbp-256]
__sbr_cell_0_2352_end:
__sbr_cell_0_2353:
    mov QWORD PTR [rbp-128], rsi
__sbr_cell_0_2353_end:
__sbr_cell_0_2354:
    mov DWORD PTR [rbp-48], edx
__sbr_cell_0_2354_end:
__sbr_cell_0_2355:
    movzx eax, dl
__sbr_cell_0_2355_end:
__sbr_cell_0_2356:
    vcvtsi2ss xmm0, xmm15, eax
__sbr_cell_0_2356_end:
ff_aac_sbr_apply.L9215_5:
__sbr_cell_0_2357:
    movzx eax, WORD PTR [rbp-130]
__sbr_cell_0_2357_end:
__sbr_cell_0_2358:
    mov esi, eax
__sbr_cell_0_2358_end:
__sbr_cell_0_2359:
    xor edx, edx
__sbr_cell_0_2359_end:
__sbr_cell_0_2360:
    mov QWORD PTR [rbp-88], r12
__sbr_cell_0_2360_end:
__sbr_cell_0_2361:
    jmp ff_aac_sbr_apply.L929e
__sbr_cell_0_2361_end:
__sbr_cell_0_2362:
    .nops 1
__sbr_cell_0_2362_end:
ff_aac_sbr_apply.L9290:
__sbr_cell_0_2363:
    cmp rdx, QWORD PTR [rbp-120]
__sbr_cell_0_2363_end:
__sbr_cell_0_2364:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2364_end:
__sbr_cell_0_2365:
    je ff_aac_sbr_apply.L91c0
__sbr_cell_0_2365_end:
ff_aac_sbr_apply.L929e:
__sbr_cell_0_2366:
    cmp rdx, 29
__sbr_cell_0_2366_end:
__sbr_cell_0_2367:
    je ff_aac_sbr_apply.L99fd
__sbr_cell_0_2367_end:
__sbr_cell_0_2368:
    movzx eax, si
__sbr_cell_0_2368_end:
__sbr_cell_0_2369:
    mov r13d, eax
__sbr_cell_0_2369_end:
__sbr_cell_0_2370:
    sub r13d, ecx
__sbr_cell_0_2370_end:
__sbr_cell_0_2371:
    mov QWORD PTR [rbp-80], rdx
__sbr_cell_0_2371_end:
__sbr_cell_0_2372:
    inc rdx
__sbr_cell_0_2372_end:
ff_aac_sbr_apply.L929e_1:
__sbr_cell_0_2373:
    mov rsi, QWORD PTR [rbp-56]
__sbr_cell_0_2373_end:
__sbr_cell_0_2374:
    movzx esi, WORD PTR [rsi+rdx*2+478226]
__sbr_cell_0_2374_end:
__sbr_cell_0_2375:
    mov ebx, esi
__sbr_cell_0_2375_end:
__sbr_cell_0_2376:
    sub ebx, ecx
__sbr_cell_0_2376_end:
__sbr_cell_0_2377:
    cmp r12, 8
__sbr_cell_0_2377_end:
__sbr_cell_0_2378:
    jae ff_aac_sbr_apply.L98bc
__sbr_cell_0_2378_end:
__sbr_cell_0_2379:
    cmp r13d, ebx
__sbr_cell_0_2379_end:
__sbr_cell_0_2380:
    jae ff_aac_sbr_apply.L93d0
__sbr_cell_0_2380_end:
__sbr_cell_0_2381:
    movsxd rax, r13d
__sbr_cell_0_2381_end:
__sbr_cell_0_2382:
    cmp rax, 49
__sbr_cell_0_2382_end:
__sbr_cell_0_2383:
    mov ebx, 48
__sbr_cell_0_2383_end:
__sbr_cell_0_2384:
    cmovae rbx, rax
__sbr_cell_0_2384_end:
__sbr_cell_0_2385:
    cmp r13d, 47
__sbr_cell_0_2385_end:
__sbr_cell_0_2386:
    mov r12, QWORD PTR [rbp-152]
__sbr_cell_0_2386_end:
__sbr_cell_0_2387:
    ja ff_aac_sbr_apply.L9a50
__sbr_cell_0_2387_end:
__sbr_cell_0_2388:
    .nops 1
__sbr_cell_0_2388_end:
ff_aac_sbr_apply.L9300:
__sbr_cell_0_2389:
    vmovss xmm1, DWORD PTR [r11+rax*4-8064]
__sbr_cell_0_2389_end:
__sbr_cell_0_2390:
    vmovss xmm2, DWORD PTR [r11+rax*4-6528]
__sbr_cell_0_2390_end:
__sbr_cell_0_2391:
    vaddss xmm3, xmm9, xmm2
__sbr_cell_0_2391_end:
__sbr_cell_0_2392:
    vdivss xmm4, xmm1, xmm3
__sbr_cell_0_2392_end:
__sbr_cell_0_2393:
    vmulss xmm5, xmm2, xmm4
__sbr_cell_0_2393_end:
__sbr_cell_0_2394:
    vsqrtss xmm5, xmm5, xmm5
__sbr_cell_0_2394_end:
__sbr_cell_0_2395:
    vmovss DWORD PTR [r11+rax*4-3072], xmm5
__sbr_cell_0_2395_end:
ff_aac_sbr_apply.L9300_1:
__sbr_cell_0_2396:
    movzx esi, BYTE PTR [r12+rax*1+0]
__sbr_cell_0_2396_end:
__sbr_cell_0_2397:
    vcvtsi2ss xmm5, xmm15, esi
__sbr_cell_0_2397_end:
__sbr_cell_0_2398:
    vmulss xmm4, xmm4, xmm5
__sbr_cell_0_2398_end:
__sbr_cell_0_2399:
    vsqrtss xmm4, xmm4, xmm4
__sbr_cell_0_2399_end:
__sbr_cell_0_2400:
    vmovss DWORD PTR [r11+rax*4-1536], xmm4
__sbr_cell_0_2400_end:
ff_aac_sbr_apply.L9300_2:
__sbr_cell_0_2401:
    cmp BYTE PTR [r10+rax*1+552032], 0
__sbr_cell_0_2401_end:
__sbr_cell_0_2402:
    je ff_aac_sbr_apply.L9370
__sbr_cell_0_2402_end:
__sbr_cell_0_2403:
    vmulss xmm1, xmm1, xmm2
__sbr_cell_0_2403_end:
__sbr_cell_0_2404:
    vaddss xmm2, xmm9, DWORD PTR [r11+rax*4-4608]
__sbr_cell_0_2404_end:
__sbr_cell_0_2405:
    vmulss xmm2, xmm3, xmm2
__sbr_cell_0_2405_end:
__sbr_cell_0_2406:
    jmp ff_aac_sbr_apply.L9386
__sbr_cell_0_2406_end:
__sbr_cell_0_2407:
    .nops 1
__sbr_cell_0_2407_end:
ff_aac_sbr_apply.L9370:
__sbr_cell_0_2408:
    vaddss xmm3, xmm9, DWORD PTR [r11+rax*4-4608]
__sbr_cell_0_2408_end:
__sbr_cell_0_2409:
    vmulss xmm2, xmm2, xmm0
__sbr_cell_0_2409_end:
__sbr_cell_0_2410:
    vaddss xmm2, xmm9, xmm2
__sbr_cell_0_2410_end:
__sbr_cell_0_2411:
    vmulss xmm2, xmm2, xmm3
__sbr_cell_0_2411_end:
ff_aac_sbr_apply.L9386:
__sbr_cell_0_2412:
    vdivss xmm1, xmm1, xmm2
__sbr_cell_0_2412_end:
__sbr_cell_0_2413:
    vsqrtss xmm1, xmm1, xmm1
__sbr_cell_0_2413_end:
__sbr_cell_0_2414:
    vaddss xmm1, xmm1, DWORD PTR [rip+LCPI14_14]
__sbr_cell_0_2414_end:
__sbr_cell_0_2415:
    vmovss DWORD PTR [r11+rax*4+0], xmm1
__sbr_cell_0_2415_end:
__sbr_cell_0_2416:
    inc rax
__sbr_cell_0_2416_end:
ff_aac_sbr_apply.L9386_1:
__sbr_cell_0_2417:
    mov rsi, QWORD PTR [rbp-56]
__sbr_cell_0_2417_end:
__sbr_cell_0_2418:
    movzx esi, WORD PTR [rsi+rdx*2+478226]
__sbr_cell_0_2418_end:
__sbr_cell_0_2419:
    movzx r15d, si
__sbr_cell_0_2419_end:
__sbr_cell_0_2420:
    mov r14d, r15d
__sbr_cell_0_2420_end:
__sbr_cell_0_2421:
    sub r14d, ecx
__sbr_cell_0_2421_end:
__sbr_cell_0_2422:
    cmp rax, r14
__sbr_cell_0_2422_end:
__sbr_cell_0_2423:
    jae ff_aac_sbr_apply.L93f0
__sbr_cell_0_2423_end:
__sbr_cell_0_2424:
    cmp rbx, rax
__sbr_cell_0_2424_end:
__sbr_cell_0_2425:
    jne ff_aac_sbr_apply.L9300
__sbr_cell_0_2425_end:
__sbr_cell_0_2426:
    jmp ff_aac_sbr_apply.L9a50
__sbr_cell_0_2426_end:
__sbr_cell_0_2427:
    .nops 1
__sbr_cell_0_2427_end:
ff_aac_sbr_apply.L93d0:
__sbr_cell_0_2428:
    vmovss xmm1, DWORD PTR [rip+LCPI14_13]
__sbr_cell_0_2428_end:
__sbr_cell_0_2429:
    vmovaps xmm2, xmm1
__sbr_cell_0_2429_end:
__sbr_cell_0_2430:
    jmp ff_aac_sbr_apply.L9530
__sbr_cell_0_2430_end:
__sbr_cell_0_2431:
    .nops 1
__sbr_cell_0_2431_end:
ff_aac_sbr_apply.L93f0:
__sbr_cell_0_2432:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_2432_end:
__sbr_cell_0_2433:
    mov rbx, QWORD PTR [rbp-80]
__sbr_cell_0_2433_end:
__sbr_cell_0_2434:
    movzx eax, WORD PTR [rax+rbx*2+478226]
__sbr_cell_0_2434_end:
__sbr_cell_0_2435:
    mov r13d, eax
__sbr_cell_0_2435_end:
__sbr_cell_0_2436:
    sub r13d, ecx
__sbr_cell_0_2436_end:
__sbr_cell_0_2437:
    cmp r13d, r14d
__sbr_cell_0_2437_end:
__sbr_cell_0_2438:
    jae ff_aac_sbr_apply.L9520
__sbr_cell_0_2438_end:
__sbr_cell_0_2439:
    lea ebx, [r13-49]
__sbr_cell_0_2439_end:
__sbr_cell_0_2440:
    mov r12d, eax
__sbr_cell_0_2440_end:
__sbr_cell_0_2441:
    sub r12d, r15d
__sbr_cell_0_2441_end:
__sbr_cell_0_2442:
    cmp ebx, r12d
__sbr_cell_0_2442_end:
__sbr_cell_0_2443:
    jae ff_aac_sbr_apply.L9bc5
__sbr_cell_0_2443_end:
__sbr_cell_0_2444:
    mov ebx, r13d
__sbr_cell_0_2444_end:
__sbr_cell_0_2445:
    mov r12d, r14d
__sbr_cell_0_2445_end:
__sbr_cell_0_2446:
    sub r12d, r13d
__sbr_cell_0_2446_end:
ff_aac_sbr_apply.L93f0_1:
__sbr_cell_0_2447:
    and r12d, 7
__sbr_cell_0_2447_end:
__sbr_cell_0_2448:
    mov QWORD PTR [rbp-104], rbx
__sbr_cell_0_2448_end:
__sbr_cell_0_2449:
    vxorps xmm1, xmm1, xmm1
__sbr_cell_0_2449_end:
__sbr_cell_0_2450:
    vxorps xmm2, xmm2, xmm2
__sbr_cell_0_2450_end:
__sbr_cell_0_2451:
    je ff_aac_sbr_apply.L9458
__sbr_cell_0_2451_end:
__sbr_cell_0_2452:
    .nops 1
__sbr_cell_0_2452_end:
ff_aac_sbr_apply.L9440:
__sbr_cell_0_2453:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+0]
__sbr_cell_0_2453_end:
__sbr_cell_0_2454:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3456]
__sbr_cell_0_2454_end:
__sbr_cell_0_2455:
    inc rbx
__sbr_cell_0_2455_end:
__sbr_cell_0_2456:
    dec r12
__sbr_cell_0_2456_end:
__sbr_cell_0_2457:
    jne ff_aac_sbr_apply.L9440
__sbr_cell_0_2457_end:
ff_aac_sbr_apply.L9458:
__sbr_cell_0_2458:
    mov r12, QWORD PTR [rbp-104]
__sbr_cell_0_2458_end:
__sbr_cell_0_2459:
    sub r12, r14
__sbr_cell_0_2459_end:
__sbr_cell_0_2460:
    cmp r12, -8
__sbr_cell_0_2460_end:
__sbr_cell_0_2461:
    ja ff_aac_sbr_apply.L9504
__sbr_cell_0_2461_end:
__sbr_cell_0_2462:
    add r15d, DWORD PTR [rbp-244]
__sbr_cell_0_2462_end:
ff_aac_sbr_apply.L9470:
__sbr_cell_0_2463:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+0]
__sbr_cell_0_2463_end:
__sbr_cell_0_2464:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3456]
__sbr_cell_0_2464_end:
__sbr_cell_0_2465:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+4]
__sbr_cell_0_2465_end:
__sbr_cell_0_2466:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3460]
__sbr_cell_0_2466_end:
__sbr_cell_0_2467:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+8]
__sbr_cell_0_2467_end:
__sbr_cell_0_2468:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3464]
__sbr_cell_0_2468_end:
__sbr_cell_0_2469:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+12]
__sbr_cell_0_2469_end:
__sbr_cell_0_2470:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3468]
__sbr_cell_0_2470_end:
__sbr_cell_0_2471:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+16]
__sbr_cell_0_2471_end:
__sbr_cell_0_2472:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3472]
__sbr_cell_0_2472_end:
__sbr_cell_0_2473:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+20]
__sbr_cell_0_2473_end:
__sbr_cell_0_2474:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3476]
__sbr_cell_0_2474_end:
__sbr_cell_0_2475:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+24]
__sbr_cell_0_2475_end:
__sbr_cell_0_2476:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3480]
__sbr_cell_0_2476_end:
__sbr_cell_0_2477:
    vaddss xmm2, xmm2, DWORD PTR [r9+rbx*4+28]
__sbr_cell_0_2477_end:
ff_aac_sbr_apply.L9470_1:
__sbr_cell_0_2478:
    vaddss xmm1, xmm1, DWORD PTR [r9+rbx*4+3484]
__sbr_cell_0_2478_end:
__sbr_cell_0_2479:
    add rbx, 8
__sbr_cell_0_2479_end:
__sbr_cell_0_2480:
    cmp r15, rbx
__sbr_cell_0_2480_end:
__sbr_cell_0_2481:
    jne ff_aac_sbr_apply.L9470
__sbr_cell_0_2481_end:
ff_aac_sbr_apply.L9504:
__sbr_cell_0_2482:
    vmovss xmm3, DWORD PTR [rip+LCPI14_13]
__sbr_cell_0_2482_end:
__sbr_cell_0_2483:
    vaddss xmm2, xmm2, xmm3
__sbr_cell_0_2483_end:
__sbr_cell_0_2484:
    vaddss xmm1, xmm1, xmm3
__sbr_cell_0_2484_end:
__sbr_cell_0_2485:
    jmp ff_aac_sbr_apply.L952c
__sbr_cell_0_2485_end:
__sbr_cell_0_2486:
    .nops 1
__sbr_cell_0_2486_end:
ff_aac_sbr_apply.L9520:
__sbr_cell_0_2487:
    vmovss xmm1, DWORD PTR [rip+LCPI14_13]
__sbr_cell_0_2487_end:
__sbr_cell_0_2488:
    vmovaps xmm2, xmm1
__sbr_cell_0_2488_end:
ff_aac_sbr_apply.L952c:
__sbr_cell_0_2489:
    mov r12, QWORD PTR [rbp-88]
__sbr_cell_0_2489_end:
ff_aac_sbr_apply.L9530:
__sbr_cell_0_2490:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_0_2490_end:
__sbr_cell_0_2491:
    mov ebx, DWORD PTR [rbx+166224]
__sbr_cell_0_2491_end:
__sbr_cell_0_2492:
    cmp rbx, 3
__sbr_cell_0_2492_end:
__sbr_cell_0_2493:
    ja ff_aac_sbr_apply.L9b72
__sbr_cell_0_2493_end:
__sbr_cell_0_2494:
    vdivss xmm1, xmm2, xmm1
__sbr_cell_0_2494_end:
__sbr_cell_0_2495:
    vsqrtss xmm1, xmm1, xmm1
__sbr_cell_0_2495_end:
__sbr_cell_0_2496:
    lea r14, [rip+limgain]
__sbr_cell_0_2496_end:
__sbr_cell_0_2497:
    vmulss xmm1, xmm1, DWORD PTR [r14+rbx*4+0]
__sbr_cell_0_2497_end:
__sbr_cell_0_2498:
    vminss xmm1, xmm1, DWORD PTR [rip+LCPI14_15]
__sbr_cell_0_2498_end:
__sbr_cell_0_2499:
    movzx ebx, si
__sbr_cell_0_2499_end:
__sbr_cell_0_2500:
    sub ebx, ecx
__sbr_cell_0_2500_end:
__sbr_cell_0_2501:
    cmp r13d, ebx
__sbr_cell_0_2501_end:
__sbr_cell_0_2502:
    jae ff_aac_sbr_apply.L9617
__sbr_cell_0_2502_end:
__sbr_cell_0_2503:
    cmp r12, 7
__sbr_cell_0_2503_end:
__sbr_cell_0_2504:
    ja ff_aac_sbr_apply.L9b81
__sbr_cell_0_2504_end:
ff_aac_sbr_apply.L9530_1:
__sbr_cell_0_2505:
    mov eax, r13d
__sbr_cell_0_2505_end:
__sbr_cell_0_2506:
    cmp rax, 49
__sbr_cell_0_2506_end:
__sbr_cell_0_2507:
    mov r14d, 48
__sbr_cell_0_2507_end:
__sbr_cell_0_2508:
    cmovae r14, rax
__sbr_cell_0_2508_end:
__sbr_cell_0_2509:
    cmp r13d, 47
__sbr_cell_0_2509_end:
__sbr_cell_0_2510:
    ja ff_aac_sbr_apply.L9a55
__sbr_cell_0_2510_end:
__sbr_cell_0_2511:
    .nops 1
__sbr_cell_0_2511_end:
ff_aac_sbr_apply.L95a0:
__sbr_cell_0_2512:
    vmovss xmm2, DWORD PTR [r8+rax*4+0]
__sbr_cell_0_2512_end:
__sbr_cell_0_2513:
    vmulss xmm3, xmm1, xmm2
__sbr_cell_0_2513_end:
__sbr_cell_0_2514:
    vmovss xmm4, DWORD PTR [r8+rax*4+3072]
__sbr_cell_0_2514_end:
__sbr_cell_0_2515:
    vdivss xmm3, xmm3, xmm4
__sbr_cell_0_2515_end:
__sbr_cell_0_2516:
    vminss xmm2, xmm3, xmm2
__sbr_cell_0_2516_end:
__sbr_cell_0_2517:
    vmovss DWORD PTR [r8+rax*4+0], xmm2
__sbr_cell_0_2517_end:
__sbr_cell_0_2518:
    vminss xmm2, xmm1, xmm4
__sbr_cell_0_2518_end:
ff_aac_sbr_apply.L95a0_1:
__sbr_cell_0_2519:
    vmovss DWORD PTR [r8+rax*4+3072], xmm2
__sbr_cell_0_2519_end:
__sbr_cell_0_2520:
    inc rax
__sbr_cell_0_2520_end:
ff_aac_sbr_apply.L95a0_2:
__sbr_cell_0_2521:
    mov rsi, QWORD PTR [rbp-56]
__sbr_cell_0_2521_end:
__sbr_cell_0_2522:
    movzx esi, WORD PTR [rsi+rdx*2+478226]
__sbr_cell_0_2522_end:
__sbr_cell_0_2523:
    mov ebx, esi
__sbr_cell_0_2523_end:
__sbr_cell_0_2524:
    sub ebx, ecx
__sbr_cell_0_2524_end:
__sbr_cell_0_2525:
    cmp rax, rbx
__sbr_cell_0_2525_end:
__sbr_cell_0_2526:
    jae ff_aac_sbr_apply.L9600
__sbr_cell_0_2526_end:
__sbr_cell_0_2527:
    cmp r14, rax
__sbr_cell_0_2527_end:
__sbr_cell_0_2528:
    jne ff_aac_sbr_apply.L95a0
__sbr_cell_0_2528_end:
__sbr_cell_0_2529:
    jmp ff_aac_sbr_apply.L9a55
__sbr_cell_0_2529_end:
__sbr_cell_0_2530:
    .nops 1
__sbr_cell_0_2530_end:
ff_aac_sbr_apply.L9600:
__sbr_cell_0_2531:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_2531_end:
__sbr_cell_0_2532:
    mov r14, QWORD PTR [rbp-80]
__sbr_cell_0_2532_end:
__sbr_cell_0_2533:
    movzx eax, WORD PTR [rax+r14*2+478226]
__sbr_cell_0_2533_end:
__sbr_cell_0_2534:
    mov r13d, eax
__sbr_cell_0_2534_end:
__sbr_cell_0_2535:
    sub r13d, ecx
__sbr_cell_0_2535_end:
ff_aac_sbr_apply.L9617:
__sbr_cell_0_2536:
    cmp r13d, ebx
__sbr_cell_0_2536_end:
__sbr_cell_0_2537:
    jae ff_aac_sbr_apply.L9820
__sbr_cell_0_2537_end:
__sbr_cell_0_2538:
    cmp r12, 7
__sbr_cell_0_2538_end:
__sbr_cell_0_2539:
    ja ff_aac_sbr_apply.L9b8b
__sbr_cell_0_2539_end:
__sbr_cell_0_2540:
    cmp r13d, 49
__sbr_cell_0_2540_end:
__sbr_cell_0_2541:
    mov r14d, 48
__sbr_cell_0_2541_end:
__sbr_cell_0_2542:
    cmovae r14d, r13d
__sbr_cell_0_2542_end:
__sbr_cell_0_2543:
    add r14d, ecx
__sbr_cell_0_2543_end:
__sbr_cell_0_2544:
    sub r14d, eax
__sbr_cell_0_2544_end:
__sbr_cell_0_2545:
    not eax
__sbr_cell_0_2545_end:
__sbr_cell_0_2546:
    add eax, ecx
__sbr_cell_0_2546_end:
__sbr_cell_0_2547:
    add eax, ebx
__sbr_cell_0_2547_end:
__sbr_cell_0_2548:
    cmp r14d, eax
__sbr_cell_0_2548_end:
__sbr_cell_0_2549:
    jbe ff_aac_sbr_apply.L9b90
__sbr_cell_0_2549_end:
__sbr_cell_0_2550:
    mov r12d, ebx
__sbr_cell_0_2550_end:
ff_aac_sbr_apply.L9617_1:
__sbr_cell_0_2551:
    mov eax, r13d
__sbr_cell_0_2551_end:
__sbr_cell_0_2552:
    mov r14d, r12d
__sbr_cell_0_2552_end:
__sbr_cell_0_2553:
    sub r14d, r13d
__sbr_cell_0_2553_end:
__sbr_cell_0_2554:
    vxorps xmm1, xmm1, xmm1
__sbr_cell_0_2554_end:
__sbr_cell_0_2555:
    mov rbx, rax
__sbr_cell_0_2555_end:
__sbr_cell_0_2556:
    vxorps xmm2, xmm2, xmm2
__sbr_cell_0_2556_end:
__sbr_cell_0_2557:
    test r14b, 1
__sbr_cell_0_2557_end:
__sbr_cell_0_2558:
    je ff_aac_sbr_apply.L96d3
__sbr_cell_0_2558_end:
__sbr_cell_0_2559:
    mov rbx, QWORD PTR [rbp-224]
__sbr_cell_0_2559_end:
__sbr_cell_0_2560:
    vmovss xmm3, DWORD PTR [rbx+rax*4+0]
__sbr_cell_0_2560_end:
__sbr_cell_0_2561:
    cmp BYTE PTR [rbp-48], 0
__sbr_cell_0_2561_end:
__sbr_cell_0_2562:
    je ff_aac_sbr_apply.L968d
__sbr_cell_0_2562_end:
__sbr_cell_0_2563:
    vcmpeqss xmm1, xmm3, xmm1
__sbr_cell_0_2563_end:
__sbr_cell_0_2564:
    vmovss xmm2, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2564_end:
__sbr_cell_0_2565:
    vandps xmm1, xmm1, xmm2
__sbr_cell_0_2565_end:
ff_aac_sbr_apply.L968d:
__sbr_cell_0_2566:
    mov rbx, QWORD PTR [rbp-96]
__sbr_cell_0_2566_end:
__sbr_cell_0_2567:
    vmovss xmm2, DWORD PTR [rbx+rax*4+0]
__sbr_cell_0_2567_end:
__sbr_cell_0_2568:
    mov rbx, QWORD PTR [rbp-128]
__sbr_cell_0_2568_end:
__sbr_cell_0_2569:
    vmovss xmm4, DWORD PTR [rbx+rax*4+0]
__sbr_cell_0_2569_end:
__sbr_cell_0_2570:
    mov rbx, QWORD PTR [rbp-216]
__sbr_cell_0_2570_end:
__sbr_cell_0_2571:
    vmulss xmm5, xmm4, DWORD PTR [rbx+rax*4+0]
__sbr_cell_0_2571_end:
__sbr_cell_0_2572:
    vmulss xmm4, xmm4, xmm5
__sbr_cell_0_2572_end:
__sbr_cell_0_2573:
    vmulss xmm3, xmm3, xmm3
__sbr_cell_0_2573_end:
__sbr_cell_0_2574:
    vaddss xmm3, xmm4, xmm3
__sbr_cell_0_2574_end:
__sbr_cell_0_2575:
    mov rbx, QWORD PTR [rbp-232]
__sbr_cell_0_2575_end:
__sbr_cell_0_2576:
    vmovss xmm4, DWORD PTR [rbx+rax*4+0]
__sbr_cell_0_2576_end:
__sbr_cell_0_2577:
    vmulss xmm1, xmm4, xmm1
__sbr_cell_0_2577_end:
__sbr_cell_0_2578:
    vmulss xmm1, xmm4, xmm1
__sbr_cell_0_2578_end:
__sbr_cell_0_2579:
    vaddss xmm1, xmm3, xmm1
__sbr_cell_0_2579_end:
__sbr_cell_0_2580:
    lea rbx, [rax+1]
__sbr_cell_0_2580_end:
ff_aac_sbr_apply.L96d3:
__sbr_cell_0_2581:
    lea r14, [r12-1]
__sbr_cell_0_2581_end:
__sbr_cell_0_2582:
    cmp r14, rax
__sbr_cell_0_2582_end:
__sbr_cell_0_2583:
    jne ff_aac_sbr_apply.L97b7
__sbr_cell_0_2583_end:
ff_aac_sbr_apply.L96e1:
__sbr_cell_0_2584:
    vmovss xmm3, DWORD PTR [rip+LCPI14_13]
__sbr_cell_0_2584_end:
__sbr_cell_0_2585:
    vaddss xmm2, xmm2, xmm3
__sbr_cell_0_2585_end:
__sbr_cell_0_2586:
    vaddss xmm1, xmm1, xmm3
__sbr_cell_0_2586_end:
__sbr_cell_0_2587:
    vdivss xmm1, xmm2, xmm1
__sbr_cell_0_2587_end:
__sbr_cell_0_2588:
    vsqrtss xmm1, xmm1, xmm1
__sbr_cell_0_2588_end:
__sbr_cell_0_2589:
    vminss xmm1, xmm1, DWORD PTR [rip+LCPI14_16]
__sbr_cell_0_2589_end:
__sbr_cell_0_2590:
    movzx ebx, si
__sbr_cell_0_2590_end:
__sbr_cell_0_2591:
    sub ebx, ecx
__sbr_cell_0_2591_end:
__sbr_cell_0_2592:
    cmp r13d, ebx
__sbr_cell_0_2592_end:
__sbr_cell_0_2593:
    mov r12, QWORD PTR [rbp-88]
__sbr_cell_0_2593_end:
__sbr_cell_0_2594:
    jae ff_aac_sbr_apply.L9290
__sbr_cell_0_2594_end:
__sbr_cell_0_2595:
    jmp ff_aac_sbr_apply.L983f
__sbr_cell_0_2595_end:
__sbr_cell_0_2596:
    .nops 1
__sbr_cell_0_2596_end:
ff_aac_sbr_apply.L9720:
__sbr_cell_0_2597:
    vcmpeqss xmm3, xmm5, xmm3
__sbr_cell_0_2597_end:
__sbr_cell_0_2598:
    vmovss xmm7, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2598_end:
__sbr_cell_0_2599:
    vandps xmm3, xmm3, xmm7
__sbr_cell_0_2599_end:
ff_aac_sbr_apply.L9731:
__sbr_cell_0_2600:
    vaddss xmm2, xmm2, DWORD PTR [rdi+rbx*4-8068]
__sbr_cell_0_2600_end:
__sbr_cell_0_2601:
    vmovss xmm7, DWORD PTR [rdi+rbx*4-4]
__sbr_cell_0_2601_end:
__sbr_cell_0_2602:
    vmulss xmm8, xmm7, DWORD PTR [rdi+rbx*4-4612]
__sbr_cell_0_2602_end:
__sbr_cell_0_2603:
    vmulss xmm7, xmm8, xmm7
__sbr_cell_0_2603_end:
__sbr_cell_0_2604:
    vmulss xmm4, xmm4, xmm4
__sbr_cell_0_2604_end:
__sbr_cell_0_2605:
    vaddss xmm4, xmm7, xmm4
__sbr_cell_0_2605_end:
__sbr_cell_0_2606:
    vmovss xmm7, DWORD PTR [rdi+rbx*4-3076]
__sbr_cell_0_2606_end:
__sbr_cell_0_2607:
    vmovss xmm8, DWORD PTR [rdi+rbx*4-3072]
__sbr_cell_0_2607_end:
__sbr_cell_0_2608:
    vmulss xmm6, xmm7, xmm6
__sbr_cell_0_2608_end:
__sbr_cell_0_2609:
    vmulss xmm6, xmm7, xmm6
__sbr_cell_0_2609_end:
__sbr_cell_0_2610:
    vaddss xmm4, xmm4, xmm6
__sbr_cell_0_2610_end:
__sbr_cell_0_2611:
    vaddss xmm1, xmm1, xmm4
__sbr_cell_0_2611_end:
__sbr_cell_0_2612:
    vaddss xmm2, xmm2, DWORD PTR [rdi+rbx*4-8064]
__sbr_cell_0_2612_end:
__sbr_cell_0_2613:
    vmovss xmm4, DWORD PTR [rdi+rbx*4+0]
__sbr_cell_0_2613_end:
__sbr_cell_0_2614:
    vmulss xmm6, xmm4, DWORD PTR [rdi+rbx*4-4608]
__sbr_cell_0_2614_end:
ff_aac_sbr_apply.L9731_1:
__sbr_cell_0_2615:
    vmulss xmm4, xmm4, xmm6
__sbr_cell_0_2615_end:
__sbr_cell_0_2616:
    vmulss xmm5, xmm5, xmm5
__sbr_cell_0_2616_end:
__sbr_cell_0_2617:
    vaddss xmm4, xmm4, xmm5
__sbr_cell_0_2617_end:
__sbr_cell_0_2618:
    vmulss xmm3, xmm8, xmm3
__sbr_cell_0_2618_end:
__sbr_cell_0_2619:
    vmulss xmm3, xmm8, xmm3
__sbr_cell_0_2619_end:
__sbr_cell_0_2620:
    vaddss xmm3, xmm4, xmm3
__sbr_cell_0_2620_end:
__sbr_cell_0_2621:
    vaddss xmm1, xmm1, xmm3
__sbr_cell_0_2621_end:
__sbr_cell_0_2622:
    add rbx, 2
__sbr_cell_0_2622_end:
__sbr_cell_0_2623:
    cmp r12, rbx
__sbr_cell_0_2623_end:
__sbr_cell_0_2624:
    je ff_aac_sbr_apply.L96e1
__sbr_cell_0_2624_end:
ff_aac_sbr_apply.L97b7:
__sbr_cell_0_2625:
    vmovss xmm4, DWORD PTR [rdi+rbx*4-1540]
__sbr_cell_0_2625_end:
__sbr_cell_0_2626:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_0_2626_end:
__sbr_cell_0_2627:
    cmp BYTE PTR [rbp-48], 0
__sbr_cell_0_2627_end:
__sbr_cell_0_2628:
    jne ff_aac_sbr_apply.L97f0
__sbr_cell_0_2628_end:
__sbr_cell_0_2629:
    vxorps xmm6, xmm6, xmm6
__sbr_cell_0_2629_end:
__sbr_cell_0_2630:
    vmovss xmm5, DWORD PTR [rdi+rbx*4-1536]
__sbr_cell_0_2630_end:
__sbr_cell_0_2631:
    je ff_aac_sbr_apply.L9731
__sbr_cell_0_2631_end:
__sbr_cell_0_2632:
    jmp ff_aac_sbr_apply.L9720
__sbr_cell_0_2632_end:
__sbr_cell_0_2633:
    .nops 1
__sbr_cell_0_2633_end:
ff_aac_sbr_apply.L97f0:
__sbr_cell_0_2634:
    vcmpeqss xmm5, xmm4, xmm3
__sbr_cell_0_2634_end:
__sbr_cell_0_2635:
    vmovss xmm6, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2635_end:
__sbr_cell_0_2636:
    vandps xmm6, xmm5, xmm6
__sbr_cell_0_2636_end:
__sbr_cell_0_2637:
    vmovss xmm5, DWORD PTR [rdi+rbx*4-1536]
__sbr_cell_0_2637_end:
__sbr_cell_0_2638:
    je ff_aac_sbr_apply.L9731
__sbr_cell_0_2638_end:
__sbr_cell_0_2639:
    jmp ff_aac_sbr_apply.L9720
__sbr_cell_0_2639_end:
__sbr_cell_0_2640:
    .nops 1
__sbr_cell_0_2640_end:
ff_aac_sbr_apply.L9820:
__sbr_cell_0_2641:
    movzx eax, si
__sbr_cell_0_2641_end:
__sbr_cell_0_2642:
    sub eax, ecx
__sbr_cell_0_2642_end:
__sbr_cell_0_2643:
    cmp r13d, eax
__sbr_cell_0_2643_end:
__sbr_cell_0_2644:
    jae ff_aac_sbr_apply.L9290
__sbr_cell_0_2644_end:
__sbr_cell_0_2645:
    cmp r12, 7
__sbr_cell_0_2645_end:
__sbr_cell_0_2646:
    ja ff_aac_sbr_apply.L9b86
__sbr_cell_0_2646_end:
__sbr_cell_0_2647:
    mov eax, r13d
__sbr_cell_0_2647_end:
__sbr_cell_0_2648:
    vmovaps xmm1, xmm9
__sbr_cell_0_2648_end:
ff_aac_sbr_apply.L983f:
__sbr_cell_0_2649:
    cmp rax, 49
__sbr_cell_0_2649_end:
__sbr_cell_0_2650:
    mov ebx, 48
__sbr_cell_0_2650_end:
__sbr_cell_0_2651:
    cmovae rbx, rax
__sbr_cell_0_2651_end:
__sbr_cell_0_2652:
    cmp rax, 47
__sbr_cell_0_2652_end:
__sbr_cell_0_2653:
    ja ff_aac_sbr_apply.L9a5a
__sbr_cell_0_2653_end:
__sbr_cell_0_2654:
    .nops 1
__sbr_cell_0_2654_end:
ff_aac_sbr_apply.L9860:
__sbr_cell_0_2655:
    vmulss xmm2, xmm1, DWORD PTR [r8+rax*4+3072]
__sbr_cell_0_2655_end:
__sbr_cell_0_2656:
    vmovss DWORD PTR [r8+rax*4+3072], xmm2
__sbr_cell_0_2656_end:
ff_aac_sbr_apply.L9860_1:
__sbr_cell_0_2657:
    vmulss xmm2, xmm1, DWORD PTR [r8+rax*4+0]
__sbr_cell_0_2657_end:
__sbr_cell_0_2658:
    vmovss DWORD PTR [r8+rax*4+0], xmm2
__sbr_cell_0_2658_end:
ff_aac_sbr_apply.L9860_2:
__sbr_cell_0_2659:
    vmulss xmm2, xmm1, DWORD PTR [r8+rax*4+1536]
__sbr_cell_0_2659_end:
__sbr_cell_0_2660:
    vmovss DWORD PTR [r8+rax*4+1536], xmm2
__sbr_cell_0_2660_end:
__sbr_cell_0_2661:
    inc rax
__sbr_cell_0_2661_end:
ff_aac_sbr_apply.L9860_3:
__sbr_cell_0_2662:
    mov rsi, QWORD PTR [rbp-56]
__sbr_cell_0_2662_end:
__sbr_cell_0_2663:
    movzx esi, WORD PTR [rsi+rdx*2+478226]
__sbr_cell_0_2663_end:
__sbr_cell_0_2664:
    mov r14d, esi
__sbr_cell_0_2664_end:
__sbr_cell_0_2665:
    sub r14d, ecx
__sbr_cell_0_2665_end:
__sbr_cell_0_2666:
    cmp rax, r14
__sbr_cell_0_2666_end:
__sbr_cell_0_2667:
    jae ff_aac_sbr_apply.L9290
__sbr_cell_0_2667_end:
__sbr_cell_0_2668:
    cmp rbx, rax
__sbr_cell_0_2668_end:
__sbr_cell_0_2669:
    jne ff_aac_sbr_apply.L9860
__sbr_cell_0_2669_end:
__sbr_cell_0_2670:
    jmp ff_aac_sbr_apply.L9a5a
__sbr_cell_0_2670_end:
ff_aac_sbr_apply.L98bc:
__sbr_cell_0_2671:
    vmovss xmm1, DWORD PTR [rip+LCPI14_13]
__sbr_cell_0_2671_end:
__sbr_cell_0_2672:
    vmovaps xmm2, xmm1
__sbr_cell_0_2672_end:
__sbr_cell_0_2673:
    cmp r13d, ebx
__sbr_cell_0_2673_end:
__sbr_cell_0_2674:
    jae ff_aac_sbr_apply.L9530
__sbr_cell_0_2674_end:
__sbr_cell_0_2675:
    jmp ff_aac_sbr_apply.L9c27
__sbr_cell_0_2675_end:
__sbr_cell_0_2676:
    .nops 1
__sbr_cell_0_2676_end:
ff_aac_sbr_apply.L98e0:
__sbr_cell_0_2677:
    mov eax, DWORD PTR [rbx+31008]
__sbr_cell_0_2677_end:
__sbr_cell_0_2678:
    cmp rax, 3
__sbr_cell_0_2678_end:
__sbr_cell_0_2679:
    jae ff_aac_sbr_apply.L9c0e
__sbr_cell_0_2679_end:
__sbr_cell_0_2680:
    imul rax, rax, 19456
__sbr_cell_0_2680_end:
__sbr_cell_0_2681:
    lea rdi, [rbx+rax*1+0]
__sbr_cell_0_2681_end:
__sbr_cell_0_2682:
    add rdi, 31024
__sbr_cell_0_2682_end:
__sbr_cell_0_2683:
    mov rsi, QWORD PTR [rbp-184]
__sbr_cell_0_2683_end:
__sbr_cell_0_2684:
    mov rdx, QWORD PTR [rbp-176]
__sbr_cell_0_2684_end:
__sbr_cell_0_2685:
    mov rcx, rbx
__sbr_cell_0_2685_end:
__sbr_cell_0_2686:
    mov r8, QWORD PTR [rbp-272]
__sbr_cell_0_2686_end:
__sbr_cell_0_2687:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_0_2687_end:
__sbr_cell_0_2688:
    vzeroupper
__sbr_cell_0_2688_end:
__sbr_cell_0_2689:
    call QWORD PTR [rax+559992]
__sbr_cell_0_2689_end:
ff_aac_sbr_apply.L9927:
__sbr_cell_0_2690:
    mov r12, QWORD PTR [rbp-280]
__sbr_cell_0_2690_end:
__sbr_cell_0_2691:
    mov eax, DWORD PTR [rbx+31008]
__sbr_cell_0_2691_end:
ff_aac_sbr_apply.L9934:
__sbr_cell_0_2692:
    mov ecx, 1
__sbr_cell_0_2692_end:
__sbr_cell_0_2693:
    sub ecx, eax
__sbr_cell_0_2693_end:
__sbr_cell_0_2694:
    cmp ecx, 3
__sbr_cell_0_2694_end:
__sbr_cell_0_2695:
    jae ff_aac_sbr_apply.L9bca
__sbr_cell_0_2695_end:
__sbr_cell_0_2696:
    cmp eax, 3
__sbr_cell_0_2696_end:
__sbr_cell_0_2697:
    mov r9, QWORD PTR [rbp-416]
__sbr_cell_0_2697_end:
__sbr_cell_0_2698:
    mov rdx, QWORD PTR [rbp-72]
__sbr_cell_0_2698_end:
__sbr_cell_0_2699:
    jae ff_aac_sbr_apply.L9bcf
__sbr_cell_0_2699_end:
__sbr_cell_0_2700:
    imul rsi, r9, 19456
__sbr_cell_0_2700_end:
__sbr_cell_0_2701:
    add rsi, QWORD PTR [rbp-168]
__sbr_cell_0_2701_end:
__sbr_cell_0_2702:
    add rdx, 31024
__sbr_cell_0_2702_end:
__sbr_cell_0_2703:
    cmp DWORD PTR [rbp-156], 1
__sbr_cell_0_2703_end:
__sbr_cell_0_2704:
    mov rdi, rdx
__sbr_cell_0_2704_end:
__sbr_cell_0_2705:
    sete bl
__sbr_cell_0_2705_end:
__sbr_cell_0_2706:
    mov ecx, ecx
__sbr_cell_0_2706_end:
ff_aac_sbr_apply.L9934_1:
__sbr_cell_0_2707:
    imul rdx, rcx, 19456
__sbr_cell_0_2707_end:
__sbr_cell_0_2708:
    add rdx, rdi
__sbr_cell_0_2708_end:
__sbr_cell_0_2709:
    mov eax, eax
__sbr_cell_0_2709_end:
__sbr_cell_0_2710:
    imul rcx, rax, 19456
__sbr_cell_0_2710_end:
__sbr_cell_0_2711:
    add rcx, rdi
__sbr_cell_0_2711_end:
__sbr_cell_0_2712:
    mov rdi, QWORD PTR [rbp-176]
__sbr_cell_0_2712_end:
__sbr_cell_0_2713:
    mov r8, QWORD PTR [rbp-192]
__sbr_cell_0_2713_end:
__sbr_cell_0_2714:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_0_2714_end:
__sbr_cell_0_2715:
    call QWORD PTR [r14+560000]
__sbr_cell_0_2715_end:
ff_aac_sbr_apply.L9934_2:
__sbr_cell_0_2716:
    mov r9, r14
__sbr_cell_0_2716_end:
__sbr_cell_0_2717:
    mov edx, 1
__sbr_cell_0_2717_end:
__sbr_cell_0_2718:
    test BYTE PTR [rbp-248], bl
__sbr_cell_0_2718_end:
__sbr_cell_0_2719:
    mov ecx, 0
__sbr_cell_0_2719_end:
__sbr_cell_0_2720:
    jne ff_aac_sbr_apply.L7682
__sbr_cell_0_2720_end:
__sbr_cell_0_2721:
    jmp ff_aac_sbr_apply.L9a02
__sbr_cell_0_2721_end:
ff_aac_sbr_apply.L99c6:
__sbr_cell_0_2722:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_0_2722_end:
__sbr_cell_0_2723:
    mov ecx, DWORD PTR [rax+8]
__sbr_cell_0_2723_end:
__sbr_cell_0_2724:
    mov eax, ecx
__sbr_cell_0_2724_end:
ff_aac_sbr_apply.L99cf:
__sbr_cell_0_2725:
    cmp ecx, 9
__sbr_cell_0_2725_end:
__sbr_cell_0_2726:
    vmovss xmm9, DWORD PTR [rip+LCPI14_5]
__sbr_cell_0_2726_end:
__sbr_cell_0_2727:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_0_2727_end:
__sbr_cell_0_2728:
    jb ff_aac_sbr_apply.L9146
__sbr_cell_0_2728_end:
__sbr_cell_0_2729:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2729_end:
ff_aac_sbr_apply.L99e9:
__sbr_cell_0_2730:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2730_end:
ff_aac_sbr_apply.L99ee:
__sbr_cell_0_2731:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2731_end:
ff_aac_sbr_apply.L99f3:
__sbr_cell_0_2732:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2732_end:
ff_aac_sbr_apply.L99f8:
__sbr_cell_0_2733:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2733_end:
ff_aac_sbr_apply.L99fd:
__sbr_cell_0_2734:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2734_end:
ff_aac_sbr_apply.L9a02:
__sbr_cell_0_2735:
    mov rbx, QWORD PTR [rbp-144]
__sbr_cell_0_2735_end:
__sbr_cell_0_2736:
    cmp DWORD PTR [rbx+22528], 1
__sbr_cell_0_2736_end:
__sbr_cell_0_2737:
    mov r14, QWORD PTR [rbp-336]
__sbr_cell_0_2737_end:
__sbr_cell_0_2738:
    jne ff_aac_sbr_apply.L9a85
__sbr_cell_0_2738_end:
__sbr_cell_0_2739:
    lea rax, [r9+528480]
__sbr_cell_0_2739_end:
__sbr_cell_0_2740:
    cmp DWORD PTR [r9+343840], 0
__sbr_cell_0_2740_end:
__sbr_cell_0_2741:
    je ff_aac_sbr_apply.L9a69
__sbr_cell_0_2741_end:
__sbr_cell_0_2742:
    lea rdi, [r9+343840]
__sbr_cell_0_2742_end:
__sbr_cell_0_2743:
    mov ecx, DWORD PTR [r9+166272]
__sbr_cell_0_2743_end:
__sbr_cell_0_2744:
    add ecx, DWORD PTR [r9+166264]
__sbr_cell_0_2744_end:
__sbr_cell_0_2745:
    mov rsi, QWORD PTR [rbp-168]
__sbr_cell_0_2745_end:
__sbr_cell_0_2746:
    mov rdx, rax
__sbr_cell_0_2746_end:
__sbr_cell_0_2747:
    call ff_ps_apply
__sbr_cell_0_2747_end:
ff_aac_sbr_apply.L9a02_1:
__sbr_cell_0_2748:
    jmp ff_aac_sbr_apply.L9a7d
__sbr_cell_0_2748_end:
ff_aac_sbr_apply.L9a50:
__sbr_cell_0_2749:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2749_end:
ff_aac_sbr_apply.L9a55:
__sbr_cell_0_2750:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2750_end:
ff_aac_sbr_apply.L9a5a:
__sbr_cell_0_2751:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2751_end:
ff_aac_sbr_apply.L9a5f:
__sbr_cell_0_2752:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2752_end:
ff_aac_sbr_apply.L9a64:
__sbr_cell_0_2753:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2753_end:
ff_aac_sbr_apply.L9a69:
__sbr_cell_0_2754:
    mov edx, 19456
__sbr_cell_0_2754_end:
__sbr_cell_0_2755:
    mov rdi, rax
__sbr_cell_0_2755_end:
__sbr_cell_0_2756:
    mov rsi, QWORD PTR [rbp-168]
__sbr_cell_0_2756_end:
__sbr_cell_0_2757:
    call memcpy
__sbr_cell_0_2757_end:
ff_aac_sbr_apply.L9a7d:
__sbr_cell_0_2758:
    mov r9, QWORD PTR [rbp-56]
__sbr_cell_0_2758_end:
__sbr_cell_0_2759:
    mov BYTE PTR [rbp-57], 1
__sbr_cell_0_2759_end:
ff_aac_sbr_apply.L9a85:
__sbr_cell_0_2760:
    mov rdi, QWORD PTR [r9+559856]
__sbr_cell_0_2760_end:
__sbr_cell_0_2761:
    mov rsi, QWORD PTR [r9+559864]
__sbr_cell_0_2761_end:
__sbr_cell_0_2762:
    mov rcx, QWORD PTR [rbx+9552]
__sbr_cell_0_2762_end:
__sbr_cell_0_2763:
    mov r15, rbx
__sbr_cell_0_2763_end:
__sbr_cell_0_2764:
    lea rax, [r9+166432]
__sbr_cell_0_2764_end:
__sbr_cell_0_2765:
    lea r10, [r9+180896]
__sbr_cell_0_2765_end:
__sbr_cell_0_2766:
    mov r13, QWORD PTR [rbp-288]
__sbr_cell_0_2766_end:
__sbr_cell_0_2767:
    mov rdx, r13
__sbr_cell_0_2767_end:
__sbr_cell_0_2768:
    mov r8, QWORD PTR [rbp-304]
__sbr_cell_0_2768_end:
__sbr_cell_0_2769:
    mov rbx, r9
__sbr_cell_0_2769_end:
__sbr_cell_0_2770:
    mov r9, QWORD PTR [rbp-168]
__sbr_cell_0_2770_end:
__sbr_cell_0_2771:
    push r14
__sbr_cell_0_2771_end:
__sbr_cell_0_2772:
    push r10
__sbr_cell_0_2772_end:
__sbr_cell_0_2773:
    push rax
__sbr_cell_0_2773_end:
__sbr_cell_0_2774:
    push r12
__sbr_cell_0_2774_end:
ff_aac_sbr_apply.L9a85_1:
__sbr_cell_0_2775:
    call sbr_qmf_synthesis
__sbr_cell_0_2775_end:
ff_aac_sbr_apply.L9a85_2:
__sbr_cell_0_2776:
    add rsp, 32
__sbr_cell_0_2776_end:
__sbr_cell_0_2777:
    cmp BYTE PTR [rbp-57], 0
__sbr_cell_0_2777_end:
__sbr_cell_0_2778:
    je ff_aac_sbr_apply.L9b24
__sbr_cell_0_2778_end:
__sbr_cell_0_2779:
    mov rdi, QWORD PTR [rbx+559856]
__sbr_cell_0_2779_end:
__sbr_cell_0_2780:
    mov rsi, QWORD PTR [rbx+559864]
__sbr_cell_0_2780_end:
__sbr_cell_0_2781:
    mov rcx, QWORD PTR [r15+9552]
__sbr_cell_0_2781_end:
__sbr_cell_0_2782:
    lea r9, [rbx+528480]
__sbr_cell_0_2782_end:
__sbr_cell_0_2783:
    lea rax, [rbx+255200]
__sbr_cell_0_2783_end:
__sbr_cell_0_2784:
    add rbx, 269664
__sbr_cell_0_2784_end:
__sbr_cell_0_2785:
    mov rdx, r13
__sbr_cell_0_2785_end:
__sbr_cell_0_2786:
    mov r8, QWORD PTR [rbp-296]
__sbr_cell_0_2786_end:
__sbr_cell_0_2787:
    push r14
__sbr_cell_0_2787_end:
__sbr_cell_0_2788:
    push rbx
__sbr_cell_0_2788_end:
__sbr_cell_0_2789:
    push rax
__sbr_cell_0_2789_end:
__sbr_cell_0_2790:
    push r12
__sbr_cell_0_2790_end:
ff_aac_sbr_apply.L9a85_3:
__sbr_cell_0_2791:
    call sbr_qmf_synthesis
__sbr_cell_0_2791_end:
ff_aac_sbr_apply.L9a85_4:
__sbr_cell_0_2792:
    add rsp, 440
__sbr_cell_0_2792_end:
__sbr_cell_0_2793:
    jmp ff_aac_sbr_apply.L9b2b
__sbr_cell_0_2793_end:
ff_aac_sbr_apply.L9b24:
__sbr_cell_0_2794:
    add rsp, 408
__sbr_cell_0_2794_end:
ff_aac_sbr_apply.L9b2b:
__sbr_cell_0_2795:
    pop rbx
__sbr_cell_0_2795_end:
__sbr_cell_0_2796:
    pop r12
__sbr_cell_0_2796_end:
__sbr_cell_0_2797:
    pop r13
__sbr_cell_0_2797_end:
__sbr_cell_0_2798:
    pop r14
__sbr_cell_0_2798_end:
__sbr_cell_0_2799:
    pop r15
__sbr_cell_0_2799_end:
__sbr_cell_0_2800:
    pop rbp
__sbr_cell_0_2800_end:
ff_aac_sbr_apply.done:
__sbr_cell_0_2801:
    ret
__sbr_cell_0_2801_end:
ff_aac_sbr_apply.L9b36:
__sbr_cell_0_2802:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2802_end:
ff_aac_sbr_apply.L9b3b:
__sbr_cell_0_2803:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2803_end:
ff_aac_sbr_apply.L9b40:
__sbr_cell_0_2804:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2804_end:
ff_aac_sbr_apply.L9b45:
__sbr_cell_0_2805:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2805_end:
ff_aac_sbr_apply.L9b4a:
__sbr_cell_0_2806:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2806_end:
ff_aac_sbr_apply.L9b4f:
__sbr_cell_0_2807:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2807_end:
ff_aac_sbr_apply.L9b54:
__sbr_cell_0_2808:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2808_end:
ff_aac_sbr_apply.L9b59:
__sbr_cell_0_2809:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2809_end:
ff_aac_sbr_apply.L9b5e:
__sbr_cell_0_2810:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2810_end:
ff_aac_sbr_apply.L9b63:
__sbr_cell_0_2811:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2811_end:
ff_aac_sbr_apply.L9b68:
__sbr_cell_0_2812:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2812_end:
ff_aac_sbr_apply.L9b6d:
__sbr_cell_0_2813:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2813_end:
ff_aac_sbr_apply.L9b72:
__sbr_cell_0_2814:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2814_end:
ff_aac_sbr_apply.L9b77:
__sbr_cell_0_2815:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2815_end:
ff_aac_sbr_apply.L9b7c:
__sbr_cell_0_2816:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2816_end:
ff_aac_sbr_apply.L9b81:
__sbr_cell_0_2817:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2817_end:
ff_aac_sbr_apply.L9b86:
__sbr_cell_0_2818:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2818_end:
ff_aac_sbr_apply.L9b8b:
__sbr_cell_0_2819:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2819_end:
ff_aac_sbr_apply.L9b90:
__sbr_cell_0_2820:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2820_end:
ff_aac_sbr_apply.L9b95:
__sbr_cell_0_2821:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2821_end:
ff_aac_sbr_apply.L9b9a:
__sbr_cell_0_2822:
    lea rdx, [rip+L_str_3]
__sbr_cell_0_2822_end:
__sbr_cell_0_2823:
    lea rcx, [rip+L_str_34]
__sbr_cell_0_2823_end:
__sbr_cell_0_2824:
    lea r8, [rip+L_src_32]
__sbr_cell_0_2824_end:
__sbr_cell_0_2825:
    xor edi, edi
__sbr_cell_0_2825_end:
__sbr_cell_0_2826:
    xor esi, esi
__sbr_cell_0_2826_end:
__sbr_cell_0_2827:
    mov r9d, 120
__sbr_cell_0_2827_end:
__sbr_cell_0_2828:
    xor eax, eax
__sbr_cell_0_2828_end:
__sbr_cell_0_2829:
    call av_log
__sbr_cell_0_2829_end:
ff_aac_sbr_apply.L9b9a_1:
__sbr_cell_0_2830:
    call abort
__sbr_cell_0_2830_end:
ff_aac_sbr_apply.L9bc5:
__sbr_cell_0_2831:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2831_end:
ff_aac_sbr_apply.L9bca:
__sbr_cell_0_2832:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2832_end:
ff_aac_sbr_apply.L9bcf:
__sbr_cell_0_2833:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2833_end:
ff_aac_sbr_apply.L9bd4:
__sbr_cell_0_2834:
    lea rdx, [rip+L_str_3]
__sbr_cell_0_2834_end:
__sbr_cell_0_2835:
    lea rcx, [rip+L_str_4]
__sbr_cell_0_2835_end:
__sbr_cell_0_2836:
    lea r8, [rip+L_str_5]
__sbr_cell_0_2836_end:
__sbr_cell_0_2837:
    xor edi, edi
__sbr_cell_0_2837_end:
__sbr_cell_0_2838:
    xor esi, esi
__sbr_cell_0_2838_end:
__sbr_cell_0_2839:
    mov r9d, 1730
__sbr_cell_0_2839_end:
__sbr_cell_0_2840:
    xor eax, eax
__sbr_cell_0_2840_end:
__sbr_cell_0_2841:
    call av_log
__sbr_cell_0_2841_end:
ff_aac_sbr_apply.L9bd4_1:
__sbr_cell_0_2842:
    call abort
__sbr_cell_0_2842_end:
ff_aac_sbr_apply.L9bff:
__sbr_cell_0_2843:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2843_end:
ff_aac_sbr_apply.L9c04:
__sbr_cell_0_2844:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2844_end:
ff_aac_sbr_apply.L9c09:
__sbr_cell_0_2845:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2845_end:
ff_aac_sbr_apply.L9c0e:
__sbr_cell_0_2846:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2846_end:
ff_aac_sbr_apply.L9c13:
__sbr_cell_0_2847:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2847_end:
ff_aac_sbr_apply.L9c18:
__sbr_cell_0_2848:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2848_end:
ff_aac_sbr_apply.L9c1d:
__sbr_cell_0_2849:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2849_end:
ff_aac_sbr_apply.L9c22:
__sbr_cell_0_2850:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2850_end:
ff_aac_sbr_apply.L9c27:
__sbr_cell_0_2851:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_0_2851_end:
__sbr_cell_0_2852:
    int3
__sbr_cell_0_2852_end:
__sbr_cell_0_2853:
    int3
__sbr_cell_0_2853_end:
__sbr_cell_0_2854:
    int3
__sbr_cell_0_2854_end:
__sbr_cell_0_2855:
    int3
__sbr_cell_0_2855_end:
.size ff_aac_sbr_apply, .-ff_aac_sbr_apply
.section .text.ff_aac_sbr_config_usac,"ax",@progbits
.globl ff_aac_sbr_config_usac
.type ff_aac_sbr_config_usac,@function
ff_aac_sbr_config_usac:
__sbr_cell_1_0:
    mov QWORD PTR [rsi+166180], 0
__sbr_cell_1_0_end:
__sbr_cell_1_1:
    mov DWORD PTR [rsi+166192], 0
__sbr_cell_1_1_end:
__sbr_cell_1_2:
    mov DWORD PTR [rsi+166264], 32
__sbr_cell_1_2_end:
__sbr_cell_1_3:
    mov DWORD PTR [rsi+166272], 0
__sbr_cell_1_3_end:
__sbr_cell_1_4:
    mov DWORD PTR [rsi+269672], 4294967295
__sbr_cell_1_4_end:
__sbr_cell_1_5:
    mov DWORD PTR [rsi+180904], 4294967295
__sbr_cell_1_5_end:
__sbr_cell_1_6:
    mov DWORD PTR [rsi+166204], 4294967295
__sbr_cell_1_6_end:
__sbr_cell_1_7:
    mov WORD PTR [rsi+166208], 65535
__sbr_cell_1_7_end:
__sbr_cell_1_8:
    xor eax, eax
__sbr_cell_1_8_end:
ff_aac_sbr_config_usac.done:
__sbr_cell_1_9:
    ret
__sbr_cell_1_9_end:
__sbr_cell_1_10:
    int3
__sbr_cell_1_10_end:
__sbr_cell_1_11:
    int3
__sbr_cell_1_11_end:
__sbr_cell_1_12:
    int3
__sbr_cell_1_12_end:
__sbr_cell_1_13:
    int3
__sbr_cell_1_13_end:
__sbr_cell_1_14:
    int3
__sbr_cell_1_14_end:
__sbr_cell_1_15:
    int3
__sbr_cell_1_15_end:
__sbr_cell_1_16:
    int3
__sbr_cell_1_16_end:
__sbr_cell_1_17:
    int3
__sbr_cell_1_17_end:
__sbr_cell_1_18:
    int3
__sbr_cell_1_18_end:
__sbr_cell_1_19:
    int3
__sbr_cell_1_19_end:
__sbr_cell_1_20:
    int3
__sbr_cell_1_20_end:
__sbr_cell_1_21:
    int3
__sbr_cell_1_21_end:
__sbr_cell_1_22:
    int3
__sbr_cell_1_22_end:
.size ff_aac_sbr_config_usac, .-ff_aac_sbr_config_usac
.section .text.ff_aac_sbr_ctx_alloc_init,"ax",@progbits
.globl ff_aac_sbr_ctx_alloc_init
.type ff_aac_sbr_ctx_alloc_init,@function
ff_aac_sbr_ctx_alloc_init:
__sbr_cell_2_0:
    push rbp
__sbr_cell_2_0_end:
__sbr_cell_2_1:
    mov rbp, rsp
__sbr_cell_2_1_end:
__sbr_cell_2_2:
    push r15
__sbr_cell_2_2_end:
__sbr_cell_2_3:
    push r14
__sbr_cell_2_3_end:
__sbr_cell_2_4:
    push rbx
__sbr_cell_2_4_end:
__sbr_cell_2_5:
    sub rsp, 24
__sbr_cell_2_5_end:
__sbr_cell_2_6:
    mov r14d, edx
__sbr_cell_2_6_end:
__sbr_cell_2_7:
    mov r15, rsi
__sbr_cell_2_7_end:
__sbr_cell_2_8:
    mov edi, 560032
__sbr_cell_2_8_end:
__sbr_cell_2_9:
    call av_mallocz
__sbr_cell_2_9_end:
ff_aac_sbr_ctx_alloc_init.L22:
__sbr_cell_2_10:
    test rax, rax
__sbr_cell_2_10_end:
__sbr_cell_2_11:
    je ff_aac_sbr_ctx_alloc_init.L17a
__sbr_cell_2_11_end:
ff_aac_sbr_ctx_alloc_init.L2b:
__sbr_cell_2_12:
    mov rbx, rax
__sbr_cell_2_12_end:
__sbr_cell_2_13:
    mov QWORD PTR [r15+0], rax
__sbr_cell_2_13_end:
__sbr_cell_2_14:
    add rax, 123168
__sbr_cell_2_14_end:
__sbr_cell_2_15:
    mov QWORD PTR [rbx+40512], rax
__sbr_cell_2_15_end:
ff_aac_sbr_ctx_alloc_init.L3e:
__sbr_cell_2_16:
    lea rax, [rbx+144672]
__sbr_cell_2_16_end:
__sbr_cell_2_17:
    mov QWORD PTR [rbx+80896], rax
__sbr_cell_2_17_end:
__sbr_cell_2_18:
    mov eax, DWORD PTR [rbx+166264]
__sbr_cell_2_18_end:
__sbr_cell_2_19:
    mov DWORD PTR [rbx+166260], eax
__sbr_cell_2_19_end:
ff_aac_sbr_ctx_alloc_init.L58:
__sbr_cell_2_20:
    mov DWORD PTR [rbx+166188], r14d
__sbr_cell_2_20_end:
__sbr_cell_2_21:
    xor eax, eax
__sbr_cell_2_21_end:
__sbr_cell_2_22:
    mov DWORD PTR [rbx+166192], eax
__sbr_cell_2_22_end:
ff_aac_sbr_ctx_alloc_init.L67:
__sbr_cell_2_23:
    mov QWORD PTR [rbx+166180], rax
__sbr_cell_2_23_end:
__sbr_cell_2_24:
    mov DWORD PTR [rbx+166264], 32
__sbr_cell_2_24_end:
ff_aac_sbr_ctx_alloc_init.L78:
__sbr_cell_2_25:
    mov DWORD PTR [rbx+166272], eax
__sbr_cell_2_25_end:
__sbr_cell_2_26:
    mov ecx, 4294967295
__sbr_cell_2_26_end:
__sbr_cell_2_27:
    mov DWORD PTR [rbx+269672], ecx
__sbr_cell_2_27_end:
ff_aac_sbr_ctx_alloc_init.L89:
__sbr_cell_2_28:
    mov DWORD PTR [rbx+180904], ecx
__sbr_cell_2_28_end:
__sbr_cell_2_29:
    mov DWORD PTR [rbx+166204], ecx
__sbr_cell_2_29_end:
ff_aac_sbr_ctx_alloc_init.L95:
__sbr_cell_2_30:
    mov WORD PTR [rbx+166208], 65535
__sbr_cell_2_30_end:
__sbr_cell_2_31:
    mov ecx, 1152
__sbr_cell_2_31_end:
__sbr_cell_2_32:
    mov DWORD PTR [rbx+180896], ecx
__sbr_cell_2_32_end:
ff_aac_sbr_ctx_alloc_init.La9:
__sbr_cell_2_33:
    mov DWORD PTR [rbx+269664], ecx
__sbr_cell_2_33_end:
__sbr_cell_2_34:
    lea r9, [rbp-28]
__sbr_cell_2_34_end:
__sbr_cell_2_35:
    mov DWORD PTR [r9+0], 889192448
__sbr_cell_2_35_end:
ff_aac_sbr_ctx_alloc_init.Lba:
__sbr_cell_2_36:
    lea rdi, [rbx+559856]
__sbr_cell_2_36_end:
__sbr_cell_2_37:
    lea rsi, [rbx+559864]
__sbr_cell_2_37_end:
__sbr_cell_2_38:
    mov QWORD PTR [rsp+0], rax
__sbr_cell_2_38_end:
__sbr_cell_2_39:
    mov edx, 1
__sbr_cell_2_39_end:
__sbr_cell_2_40:
    mov ecx, 1
__sbr_cell_2_40_end:
__sbr_cell_2_41:
    mov r8d, 64
__sbr_cell_2_41_end:
__sbr_cell_2_42:
    call av_tx_init
__sbr_cell_2_42_end:
ff_aac_sbr_ctx_alloc_init.Le1:
__sbr_cell_2_43:
    test eax, eax
__sbr_cell_2_43_end:
__sbr_cell_2_44:
    js ff_aac_sbr_ctx_alloc_init.L17f
__sbr_cell_2_44_end:
ff_aac_sbr_ctx_alloc_init.Le9:
__sbr_cell_2_45:
    lea r9, [rbp-28]
__sbr_cell_2_45_end:
__sbr_cell_2_46:
    mov DWORD PTR [r9+0], 3347054592
__sbr_cell_2_46_end:
__sbr_cell_2_47:
    lea rdi, [rbx+559840]
__sbr_cell_2_47_end:
__sbr_cell_2_48:
    lea rsi, [rbx+559848]
__sbr_cell_2_48_end:
__sbr_cell_2_49:
    mov QWORD PTR [rsp+0], 0
__sbr_cell_2_49_end:
__sbr_cell_2_50:
    mov edx, 1
__sbr_cell_2_50_end:
__sbr_cell_2_51:
    mov ecx, 1
__sbr_cell_2_51_end:
__sbr_cell_2_52:
    mov r8d, 64
__sbr_cell_2_52_end:
__sbr_cell_2_53:
    call av_tx_init
__sbr_cell_2_53_end:
ff_aac_sbr_ctx_alloc_init.L11f:
__sbr_cell_2_54:
    test eax, eax
__sbr_cell_2_54_end:
__sbr_cell_2_55:
    js ff_aac_sbr_ctx_alloc_init.L17f
__sbr_cell_2_55_end:
ff_aac_sbr_ctx_alloc_init.L123:
__sbr_cell_2_56:
    lea rdi, [rbx+477880]
__sbr_cell_2_56_end:
__sbr_cell_2_57:
    call ff_psdsp_init
__sbr_cell_2_57_end:
ff_aac_sbr_ctx_alloc_init.L12f:
__sbr_cell_2_58:
    mov rdi, rbx
__sbr_cell_2_58_end:
__sbr_cell_2_59:
    add rdi, 559872
__sbr_cell_2_59_end:
__sbr_cell_2_60:
    call ff_sbrdsp_init
__sbr_cell_2_60_end:
ff_aac_sbr_ctx_alloc_init.L13e:
__sbr_cell_2_61:
    lea rax, [rip+sbr_lf_gen]
__sbr_cell_2_61_end:
__sbr_cell_2_62:
    mov QWORD PTR [rbx+559984], rax
__sbr_cell_2_62_end:
__sbr_cell_2_63:
    lea rax, [rip+sbr_hf_assemble]
__sbr_cell_2_63_end:
__sbr_cell_2_64:
    mov QWORD PTR [rbx+559992], rax
__sbr_cell_2_64_end:
ff_aac_sbr_ctx_alloc_init.L15a:
__sbr_cell_2_65:
    lea rax, [rip+sbr_x_gen]
__sbr_cell_2_65_end:
__sbr_cell_2_66:
    mov QWORD PTR [rbx+560000], rax
__sbr_cell_2_66_end:
__sbr_cell_2_67:
    lea rax, [rip+sbr_hf_inverse_filter]
__sbr_cell_2_67_end:
__sbr_cell_2_68:
    mov QWORD PTR [rbx+560008], rax
__sbr_cell_2_68_end:
__sbr_cell_2_69:
    xor eax, eax
__sbr_cell_2_69_end:
__sbr_cell_2_70:
    jmp ff_aac_sbr_ctx_alloc_init.L17f
__sbr_cell_2_70_end:
ff_aac_sbr_ctx_alloc_init.L17a:
__sbr_cell_2_71:
    mov eax, 4294967284
__sbr_cell_2_71_end:
ff_aac_sbr_ctx_alloc_init.L17f:
__sbr_cell_2_72:
    add rsp, 24
__sbr_cell_2_72_end:
__sbr_cell_2_73:
    pop rbx
__sbr_cell_2_73_end:
__sbr_cell_2_74:
    pop r14
__sbr_cell_2_74_end:
__sbr_cell_2_75:
    pop r15
__sbr_cell_2_75_end:
__sbr_cell_2_76:
    pop rbp
__sbr_cell_2_76_end:
ff_aac_sbr_ctx_alloc_init.done:
__sbr_cell_2_77:
    ret
__sbr_cell_2_77_end:
.size ff_aac_sbr_ctx_alloc_init, .-ff_aac_sbr_ctx_alloc_init
.section .text.ff_aac_sbr_decode_extension,"ax",@progbits
.globl ff_aac_sbr_decode_extension
.type ff_aac_sbr_decode_extension,@function
ff_aac_sbr_decode_extension:
__sbr_cell_3_0:
    push rbp
__sbr_cell_3_0_end:
__sbr_cell_3_1:
    mov rbp, rsp
__sbr_cell_3_1_end:
__sbr_cell_3_2:
    push r15
__sbr_cell_3_2_end:
__sbr_cell_3_3:
    push r14
__sbr_cell_3_3_end:
__sbr_cell_3_4:
    push r13
__sbr_cell_3_4_end:
__sbr_cell_3_5:
    push r12
__sbr_cell_3_5_end:
__sbr_cell_3_6:
    push rbx
__sbr_cell_3_6_end:
__sbr_cell_3_7:
    sub rsp, 56
__sbr_cell_3_7_end:
__sbr_cell_3_8:
    mov r13d, r9d
__sbr_cell_3_8_end:
__sbr_cell_3_9:
    mov r14, rsi
__sbr_cell_3_9_end:
__sbr_cell_3_10:
    mov r12, rdi
__sbr_cell_3_10_end:
__sbr_cell_3_11:
    lea rdi, [rsi+166176]
__sbr_cell_3_11_end:
ff_aac_sbr_decode_extension.L21:
__sbr_cell_3_12:
    mov rax, QWORD PTR [rdx+16]
__sbr_cell_3_12_end:
__sbr_cell_3_13:
    mov QWORD PTR [rbp-48], rax
__sbr_cell_3_13_end:
__sbr_cell_3_14:
    vmovups xmm0, XMMWORD PTR [rdx+0]
__sbr_cell_3_14_end:
__sbr_cell_3_15:
    vmovaps XMMWORD PTR [rbp-64], xmm0
__sbr_cell_3_15_end:
__sbr_cell_3_16:
    mov QWORD PTR [rbp-80], r8
__sbr_cell_3_16_end:
ff_aac_sbr_decode_extension.L36:
__sbr_cell_3_17:
    lea eax, [r8*8-4]
__sbr_cell_3_17_end:
__sbr_cell_3_18:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_3_18_end:
__sbr_cell_3_19:
    mov r9d, DWORD PTR [rdx+16]
__sbr_cell_3_19_end:
__sbr_cell_3_20:
    mov r8d, esi
__sbr_cell_3_20_end:
__sbr_cell_3_21:
    neg r8d
__sbr_cell_3_21_end:
__sbr_cell_3_22:
    sub r9d, esi
__sbr_cell_3_22_end:
__sbr_cell_3_23:
    cmp eax, r9d
__sbr_cell_3_23_end:
__sbr_cell_3_24:
    cmovl r9d, eax
__sbr_cell_3_24_end:
__sbr_cell_3_25:
    cmp eax, r8d
__sbr_cell_3_25_end:
__sbr_cell_3_26:
    cmovl r9d, r8d
__sbr_cell_3_26_end:
__sbr_cell_3_27:
    add r9d, esi
__sbr_cell_3_27_end:
__sbr_cell_3_28:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_3_28_end:
ff_aac_sbr_decode_extension.L63:
__sbr_cell_3_29:
    mov DWORD PTR [r14+166200], 0
__sbr_cell_3_29_end:
__sbr_cell_3_30:
    cmp DWORD PTR [r14+166176], 0
__sbr_cell_3_30_end:
__sbr_cell_3_31:
    je ff_aac_sbr_decode_extension.L301
__sbr_cell_3_31_end:
__sbr_cell_3_32:
    cmp DWORD PTR [r12+22516], 0
__sbr_cell_3_32_end:
__sbr_cell_3_33:
    je ff_aac_sbr_decode_extension.L31c
__sbr_cell_3_33_end:
ff_aac_sbr_decode_extension.L8b:
__sbr_cell_3_34:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_3_34_end:
__sbr_cell_3_35:
    mov esi, DWORD PTR [rbp-48]
__sbr_cell_3_35_end:
__sbr_cell_3_36:
    lea eax, [rdx+10]
__sbr_cell_3_36_end:
__sbr_cell_3_37:
    cmp esi, eax
__sbr_cell_3_37_end:
__sbr_cell_3_38:
    cmovb eax, esi
__sbr_cell_3_38_end:
__sbr_cell_3_39:
    test ecx, ecx
__sbr_cell_3_39_end:
__sbr_cell_3_40:
    cmove eax, edx
__sbr_cell_3_40_end:
__sbr_cell_3_41:
    mov ecx, 1
__sbr_cell_3_41_end:
__sbr_cell_3_42:
    mov r15d, 11
__sbr_cell_3_42_end:
__sbr_cell_3_43:
    cmove r15d, ecx
__sbr_cell_3_43_end:
ff_aac_sbr_decode_extension.Lad:
__sbr_cell_3_44:
    mov ecx, DWORD PTR [r14+166264]
__sbr_cell_3_44_end:
__sbr_cell_3_45:
    mov edx, DWORD PTR [r14+166272]
__sbr_cell_3_45_end:
__sbr_cell_3_46:
    mov DWORD PTR [r14+166260], ecx
__sbr_cell_3_46_end:
__sbr_cell_3_47:
    mov DWORD PTR [r14+166268], edx
__sbr_cell_3_47_end:
__sbr_cell_3_48:
    mov DWORD PTR [r14+166276], 1
__sbr_cell_3_48_end:
ff_aac_sbr_decode_extension.Ld4:
__sbr_cell_3_49:
    mov rcx, QWORD PTR [rbp-64]
__sbr_cell_3_49_end:
__sbr_cell_3_50:
    mov edx, eax
__sbr_cell_3_50_end:
__sbr_cell_3_51:
    shr edx, 3
__sbr_cell_3_51_end:
__sbr_cell_3_52:
    xor r8d, r8d
__sbr_cell_3_52_end:
__sbr_cell_3_53:
    cmp eax, esi
__sbr_cell_3_53_end:
__sbr_cell_3_54:
    setl r8b
__sbr_cell_3_54_end:
__sbr_cell_3_55:
    add r8d, eax
__sbr_cell_3_55_end:
__sbr_cell_3_56:
    movzx edx, BYTE PTR [rcx+rdx*1+0]
__sbr_cell_3_56_end:
__sbr_cell_3_57:
    mov DWORD PTR [rbp-56], r8d
__sbr_cell_3_57_end:
__sbr_cell_3_58:
    and al, 7
__sbr_cell_3_58_end:
__sbr_cell_3_59:
    mov ecx, eax
__sbr_cell_3_59_end:
__sbr_cell_3_60:
    shl edx, cl
__sbr_cell_3_60_end:
__sbr_cell_3_61:
    test dl, dl
__sbr_cell_3_61_end:
__sbr_cell_3_62:
    jns ff_aac_sbr_decode_extension.L333
__sbr_cell_3_62_end:
ff_aac_sbr_decode_extension.Lff:
__sbr_cell_3_63:
    lea rsi, [rbp-64]
__sbr_cell_3_63_end:
__sbr_cell_3_64:
    mov rbx, rdi
__sbr_cell_3_64_end:
__sbr_cell_3_65:
    xor edx, edx
__sbr_cell_3_65_end:
__sbr_cell_3_66:
    call read_sbr_header
__sbr_cell_3_66_end:
ff_aac_sbr_decode_extension.L10d:
__sbr_cell_3_67:
    add eax, r15d
__sbr_cell_3_67_end:
__sbr_cell_3_68:
    mov r15d, eax
__sbr_cell_3_68_end:
__sbr_cell_3_69:
    cmp DWORD PTR [r14+166200], 0
__sbr_cell_3_69_end:
__sbr_cell_3_70:
    je ff_aac_sbr_decode_extension.L128
__sbr_cell_3_70_end:
ff_aac_sbr_decode_extension.L11d:
__sbr_cell_3_71:
    mov rdi, r12
__sbr_cell_3_71_end:
__sbr_cell_3_72:
    mov rsi, rbx
__sbr_cell_3_72_end:
__sbr_cell_3_73:
    call sbr_reset
__sbr_cell_3_73_end:
ff_aac_sbr_decode_extension.L128:
__sbr_cell_3_74:
    cmp DWORD PTR [r14+166180], 0
__sbr_cell_3_74_end:
__sbr_cell_3_75:
    je ff_aac_sbr_decode_extension.L4ee
__sbr_cell_3_75_end:
__sbr_cell_3_76:
    mov rsi, rbx
__sbr_cell_3_76_end:
__sbr_cell_3_77:
    mov r8d, DWORD PTR [rbp-56]
__sbr_cell_3_77_end:
__sbr_cell_3_78:
    mov DWORD PTR [r14+166188], r13d
__sbr_cell_3_78_end:
__sbr_cell_3_79:
    mov DWORD PTR [r14+166184], 1
__sbr_cell_3_79_end:
__sbr_cell_3_80:
    test r13d, 4294967293
__sbr_cell_3_80_end:
__sbr_cell_3_81:
    mov QWORD PTR [rbp-72], r12
__sbr_cell_3_81_end:
__sbr_cell_3_82:
    mov QWORD PTR [rbp-88], r8
__sbr_cell_3_82_end:
__sbr_cell_3_83:
    je ff_aac_sbr_decode_extension.L349
__sbr_cell_3_83_end:
ff_aac_sbr_decode_extension.L164:
__sbr_cell_3_84:
    cmp r13d, 1
__sbr_cell_3_84_end:
__sbr_cell_3_85:
    jne ff_aac_sbr_decode_extension.L466
__sbr_cell_3_85_end:
ff_aac_sbr_decode_extension.L16e:
__sbr_cell_3_86:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_3_86_end:
__sbr_cell_3_87:
    mov ecx, r8d
__sbr_cell_3_87_end:
__sbr_cell_3_88:
    shr ecx, 3
__sbr_cell_3_88_end:
__sbr_cell_3_89:
    mov edx, DWORD PTR [rbp-48]
__sbr_cell_3_89_end:
__sbr_cell_3_90:
    xor r9d, r9d
__sbr_cell_3_90_end:
__sbr_cell_3_91:
    cmp r8d, edx
__sbr_cell_3_91_end:
__sbr_cell_3_92:
    setl r9b
__sbr_cell_3_92_end:
__sbr_cell_3_93:
    movzx edi, BYTE PTR [rax+rcx*1+0]
__sbr_cell_3_93_end:
__sbr_cell_3_94:
    mov ecx, r8d
__sbr_cell_3_94_end:
__sbr_cell_3_95:
    and cl, 7
__sbr_cell_3_95_end:
__sbr_cell_3_96:
    shl edi, cl
__sbr_cell_3_96_end:
__sbr_cell_3_97:
    lea ecx, [r8+r9*1+0]
__sbr_cell_3_97_end:
__sbr_cell_3_98:
    add ecx, 8
__sbr_cell_3_98_end:
__sbr_cell_3_99:
    cmp edx, ecx
__sbr_cell_3_99_end:
__sbr_cell_3_100:
    cmovb ecx, edx
__sbr_cell_3_100_end:
__sbr_cell_3_101:
    add r8d, r9d
__sbr_cell_3_101_end:
__sbr_cell_3_102:
    test dil, dil
__sbr_cell_3_102_end:
__sbr_cell_3_103:
    cmovns ecx, r8d
__sbr_cell_3_103_end:
ff_aac_sbr_decode_extension.L1a7:
__sbr_cell_3_104:
    mov r8d, ecx
__sbr_cell_3_104_end:
__sbr_cell_3_105:
    shr r8d, 3
__sbr_cell_3_105_end:
__sbr_cell_3_106:
    xor edi, edi
__sbr_cell_3_106_end:
__sbr_cell_3_107:
    cmp ecx, edx
__sbr_cell_3_107_end:
__sbr_cell_3_108:
    setl dil
__sbr_cell_3_108_end:
__sbr_cell_3_109:
    add edi, ecx
__sbr_cell_3_109_end:
__sbr_cell_3_110:
    movzx ebx, BYTE PTR [rax+r8*1+0]
__sbr_cell_3_110_end:
__sbr_cell_3_111:
    and cl, 7
__sbr_cell_3_111_end:
__sbr_cell_3_112:
    shl ebx, cl
__sbr_cell_3_112_end:
__sbr_cell_3_113:
    shr ebx, 7
__sbr_cell_3_113_end:
__sbr_cell_3_114:
    mov DWORD PTR [rbp-56], edi
__sbr_cell_3_114_end:
__sbr_cell_3_115:
    mov eax, ebx
__sbr_cell_3_115_end:
__sbr_cell_3_116:
    and eax, 1
__sbr_cell_3_116_end:
__sbr_cell_3_117:
    mov DWORD PTR [r14+166236], eax
__sbr_cell_3_117_end:
ff_aac_sbr_decode_extension.L1d4:
__sbr_cell_3_118:
    lea r13, [r14+166304]
__sbr_cell_3_118_end:
__sbr_cell_3_119:
    lea rdx, [rbp-64]
__sbr_cell_3_119_end:
__sbr_cell_3_120:
    mov rdi, r12
__sbr_cell_3_120_end:
__sbr_cell_3_121:
    mov rcx, r13
__sbr_cell_3_121_end:
__sbr_cell_3_122:
    call read_sbr_grid
__sbr_cell_3_122_end:
ff_aac_sbr_decode_extension.L1ea:
__sbr_cell_3_123:
    and ebx, 1
__sbr_cell_3_123_end:
__sbr_cell_3_124:
    jne ff_aac_sbr_decode_extension.L483
__sbr_cell_3_124_end:
__sbr_cell_3_125:
    test eax, eax
__sbr_cell_3_125_end:
__sbr_cell_3_126:
    jne ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_126_end:
__sbr_cell_3_127:
    lea rcx, [r14+255072]
__sbr_cell_3_127_end:
__sbr_cell_3_128:
    lea rdx, [rbp-64]
__sbr_cell_3_128_end:
__sbr_cell_3_129:
    mov rdi, r12
__sbr_cell_3_129_end:
__sbr_cell_3_130:
    lea rsi, [r14+166176]
__sbr_cell_3_130_end:
__sbr_cell_3_131:
    call read_sbr_grid
__sbr_cell_3_131_end:
ff_aac_sbr_decode_extension.L215:
__sbr_cell_3_132:
    test eax, eax
__sbr_cell_3_132_end:
__sbr_cell_3_133:
    jne ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_133_end:
__sbr_cell_3_134:
    mov edi, DWORD PTR [r14+166192]
__sbr_cell_3_134_end:
__sbr_cell_3_135:
    lea r13, [rbp-64]
__sbr_cell_3_135_end:
__sbr_cell_3_136:
    mov rsi, r13
__sbr_cell_3_136_end:
__sbr_cell_3_137:
    lea rdx, [r14+166304]
__sbr_cell_3_137_end:
__sbr_cell_3_138:
    xor ecx, ecx
__sbr_cell_3_138_end:
__sbr_cell_3_139:
    call read_sbr_dtdf
__sbr_cell_3_139_end:
ff_aac_sbr_decode_extension.L239:
__sbr_cell_3_140:
    mov edi, DWORD PTR [r14+166192]
__sbr_cell_3_140_end:
__sbr_cell_3_141:
    mov rsi, r13
__sbr_cell_3_141_end:
__sbr_cell_3_142:
    lea rdx, [r14+255072]
__sbr_cell_3_142_end:
__sbr_cell_3_143:
    xor ecx, ecx
__sbr_cell_3_143_end:
__sbr_cell_3_144:
    call read_sbr_dtdf
__sbr_cell_3_144_end:
ff_aac_sbr_decode_extension.L251:
__sbr_cell_3_145:
    lea rbx, [r14+166176]
__sbr_cell_3_145_end:
__sbr_cell_3_146:
    mov rdi, rbx
__sbr_cell_3_146_end:
__sbr_cell_3_147:
    mov rsi, r13
__sbr_cell_3_147_end:
__sbr_cell_3_148:
    lea rdx, [r14+166304]
__sbr_cell_3_148_end:
__sbr_cell_3_149:
    call read_sbr_invf
__sbr_cell_3_149_end:
ff_aac_sbr_decode_extension.L26a:
__sbr_cell_3_150:
    mov rdi, rbx
__sbr_cell_3_150_end:
__sbr_cell_3_151:
    mov rsi, r13
__sbr_cell_3_151_end:
__sbr_cell_3_152:
    lea rdx, [r14+255072]
__sbr_cell_3_152_end:
__sbr_cell_3_153:
    call read_sbr_invf
__sbr_cell_3_153_end:
ff_aac_sbr_decode_extension.L27c:
__sbr_cell_3_154:
    mov rdi, r12
__sbr_cell_3_154_end:
__sbr_cell_3_155:
    mov rsi, rbx
__sbr_cell_3_155_end:
__sbr_cell_3_156:
    mov rdx, r13
__sbr_cell_3_156_end:
__sbr_cell_3_157:
    lea r13, [r14+255072]
__sbr_cell_3_157_end:
__sbr_cell_3_158:
    lea rbx, [r14+166304]
__sbr_cell_3_158_end:
__sbr_cell_3_159:
    mov rcx, rbx
__sbr_cell_3_159_end:
__sbr_cell_3_160:
    xor r8d, r8d
__sbr_cell_3_160_end:
__sbr_cell_3_161:
    call read_sbr_envelope
__sbr_cell_3_161_end:
ff_aac_sbr_decode_extension.L29e:
__sbr_cell_3_162:
    test eax, eax
__sbr_cell_3_162_end:
__sbr_cell_3_163:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_163_end:
__sbr_cell_3_164:
    lea rdx, [rbp-64]
__sbr_cell_3_164_end:
__sbr_cell_3_165:
    mov rdi, r12
__sbr_cell_3_165_end:
__sbr_cell_3_166:
    lea rsi, [r14+166176]
__sbr_cell_3_166_end:
__sbr_cell_3_167:
    mov rcx, r13
__sbr_cell_3_167_end:
__sbr_cell_3_168:
    mov r8d, 1
__sbr_cell_3_168_end:
__sbr_cell_3_169:
    call read_sbr_envelope
__sbr_cell_3_169_end:
ff_aac_sbr_decode_extension.L2c2:
__sbr_cell_3_170:
    test eax, eax
__sbr_cell_3_170_end:
__sbr_cell_3_171:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_171_end:
__sbr_cell_3_172:
    lea rdx, [rbp-64]
__sbr_cell_3_172_end:
__sbr_cell_3_173:
    mov rdi, r12
__sbr_cell_3_173_end:
__sbr_cell_3_174:
    lea rsi, [r14+166176]
__sbr_cell_3_174_end:
__sbr_cell_3_175:
    mov rcx, rbx
__sbr_cell_3_175_end:
__sbr_cell_3_176:
    xor r8d, r8d
__sbr_cell_3_176_end:
__sbr_cell_3_177:
    call read_sbr_noise
__sbr_cell_3_177_end:
ff_aac_sbr_decode_extension.L2e3:
__sbr_cell_3_178:
    test eax, eax
__sbr_cell_3_178_end:
__sbr_cell_3_179:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_179_end:
__sbr_cell_3_180:
    lea rdx, [rbp-64]
__sbr_cell_3_180_end:
__sbr_cell_3_181:
    mov rdi, r12
__sbr_cell_3_181_end:
__sbr_cell_3_182:
    lea rsi, [r14+166176]
__sbr_cell_3_182_end:
__sbr_cell_3_183:
    mov rcx, r13
__sbr_cell_3_183_end:
__sbr_cell_3_184:
    jmp ff_aac_sbr_decode_extension.L76e
__sbr_cell_3_184_end:
ff_aac_sbr_decode_extension.L301:
__sbr_cell_3_185:
    mov eax, DWORD PTR [r12+22496]
__sbr_cell_3_185_end:
__sbr_cell_3_186:
    add eax, eax
__sbr_cell_3_186_end:
__sbr_cell_3_187:
    mov DWORD PTR [rdi+0], eax
__sbr_cell_3_187_end:
__sbr_cell_3_188:
    cmp DWORD PTR [r12+22516], 0
__sbr_cell_3_188_end:
__sbr_cell_3_189:
    jne ff_aac_sbr_decode_extension.L8b
__sbr_cell_3_189_end:
ff_aac_sbr_decode_extension.L31c:
__sbr_cell_3_190:
    mov eax, DWORD PTR [r12+22496]
__sbr_cell_3_190_end:
__sbr_cell_3_191:
    add eax, eax
__sbr_cell_3_191_end:
__sbr_cell_3_192:
    mov DWORD PTR [r12+22516], eax
__sbr_cell_3_192_end:
__sbr_cell_3_193:
    jmp ff_aac_sbr_decode_extension.L8b
__sbr_cell_3_193_end:
ff_aac_sbr_decode_extension.L333:
__sbr_cell_3_194:
    mov rbx, rdi
__sbr_cell_3_194_end:
__sbr_cell_3_195:
    cmp DWORD PTR [r14+166200], 0
__sbr_cell_3_195_end:
__sbr_cell_3_196:
    jne ff_aac_sbr_decode_extension.L11d
__sbr_cell_3_196_end:
__sbr_cell_3_197:
    jmp ff_aac_sbr_decode_extension.L128
__sbr_cell_3_197_end:
ff_aac_sbr_decode_extension.L349:
__sbr_cell_3_198:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_3_198_end:
__sbr_cell_3_199:
    mov ecx, r8d
__sbr_cell_3_199_end:
__sbr_cell_3_200:
    shr ecx, 3
__sbr_cell_3_200_end:
__sbr_cell_3_201:
    mov edx, DWORD PTR [rbp-48]
__sbr_cell_3_201_end:
__sbr_cell_3_202:
    xor r9d, r9d
__sbr_cell_3_202_end:
__sbr_cell_3_203:
    cmp r8d, edx
__sbr_cell_3_203_end:
__sbr_cell_3_204:
    setl r9b
__sbr_cell_3_204_end:
__sbr_cell_3_205:
    lea edi, [r8+r9*1+0]
__sbr_cell_3_205_end:
__sbr_cell_3_206:
    movzx eax, BYTE PTR [rax+rcx*1+0]
__sbr_cell_3_206_end:
__sbr_cell_3_207:
    mov ecx, r8d
__sbr_cell_3_207_end:
__sbr_cell_3_208:
    and cl, 7
__sbr_cell_3_208_end:
__sbr_cell_3_209:
    shl eax, cl
__sbr_cell_3_209_end:
__sbr_cell_3_210:
    lea ecx, [r8+r9*1+0]
__sbr_cell_3_210_end:
__sbr_cell_3_211:
    add ecx, 4
__sbr_cell_3_211_end:
__sbr_cell_3_212:
    cmp edx, ecx
__sbr_cell_3_212_end:
__sbr_cell_3_213:
    cmovb ecx, edx
__sbr_cell_3_213_end:
__sbr_cell_3_214:
    test al, al
__sbr_cell_3_214_end:
__sbr_cell_3_215:
    cmovns ecx, edi
__sbr_cell_3_215_end:
__sbr_cell_3_216:
    mov DWORD PTR [rbp-56], ecx
__sbr_cell_3_216_end:
ff_aac_sbr_decode_extension.L384:
__sbr_cell_3_217:
    lea r13, [r14+166304]
__sbr_cell_3_217_end:
__sbr_cell_3_218:
    lea rdx, [rbp-64]
__sbr_cell_3_218_end:
__sbr_cell_3_219:
    mov rdi, r12
__sbr_cell_3_219_end:
__sbr_cell_3_220:
    mov rcx, r13
__sbr_cell_3_220_end:
__sbr_cell_3_221:
    mov r12, rsi
__sbr_cell_3_221_end:
__sbr_cell_3_222:
    call read_sbr_grid
__sbr_cell_3_222_end:
ff_aac_sbr_decode_extension.L39d:
__sbr_cell_3_223:
    test eax, eax
__sbr_cell_3_223_end:
__sbr_cell_3_224:
    jne ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_224_end:
__sbr_cell_3_225:
    mov edi, DWORD PTR [r14+166192]
__sbr_cell_3_225_end:
__sbr_cell_3_226:
    lea rbx, [rbp-64]
__sbr_cell_3_226_end:
__sbr_cell_3_227:
    mov rsi, rbx
__sbr_cell_3_227_end:
__sbr_cell_3_228:
    mov rdx, r13
__sbr_cell_3_228_end:
__sbr_cell_3_229:
    xor ecx, ecx
__sbr_cell_3_229_end:
__sbr_cell_3_230:
    call read_sbr_dtdf
__sbr_cell_3_230_end:
ff_aac_sbr_decode_extension.L3bd:
__sbr_cell_3_231:
    mov rdi, r12
__sbr_cell_3_231_end:
__sbr_cell_3_232:
    mov rsi, rbx
__sbr_cell_3_232_end:
__sbr_cell_3_233:
    mov rdx, r13
__sbr_cell_3_233_end:
__sbr_cell_3_234:
    call read_sbr_invf
__sbr_cell_3_234_end:
ff_aac_sbr_decode_extension.L3cb:
__sbr_cell_3_235:
    mov rdi, QWORD PTR [rbp-72]
__sbr_cell_3_235_end:
__sbr_cell_3_236:
    mov rsi, r12
__sbr_cell_3_236_end:
__sbr_cell_3_237:
    mov rdx, rbx
__sbr_cell_3_237_end:
__sbr_cell_3_238:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_3_238_end:
__sbr_cell_3_239:
    mov rcx, r13
__sbr_cell_3_239_end:
__sbr_cell_3_240:
    xor r8d, r8d
__sbr_cell_3_240_end:
__sbr_cell_3_241:
    call read_sbr_envelope
__sbr_cell_3_241_end:
ff_aac_sbr_decode_extension.L3e4:
__sbr_cell_3_242:
    test eax, eax
__sbr_cell_3_242_end:
__sbr_cell_3_243:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_243_end:
__sbr_cell_3_244:
    lea rdx, [rbp-64]
__sbr_cell_3_244_end:
__sbr_cell_3_245:
    mov rdi, rbx
__sbr_cell_3_245_end:
__sbr_cell_3_246:
    mov rsi, r12
__sbr_cell_3_246_end:
__sbr_cell_3_247:
    mov rcx, r13
__sbr_cell_3_247_end:
__sbr_cell_3_248:
    xor r8d, r8d
__sbr_cell_3_248_end:
__sbr_cell_3_249:
    call read_sbr_noise
__sbr_cell_3_249_end:
ff_aac_sbr_decode_extension.L401:
__sbr_cell_3_250:
    test eax, eax
__sbr_cell_3_250_end:
__sbr_cell_3_251:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_251_end:
ff_aac_sbr_decode_extension.L409:
__sbr_cell_3_252:
    mov ecx, DWORD PTR [rbp-56]
__sbr_cell_3_252_end:
__sbr_cell_3_253:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_3_253_end:
__sbr_cell_3_254:
    mov edx, ecx
__sbr_cell_3_254_end:
__sbr_cell_3_255:
    shr edx, 3
__sbr_cell_3_255_end:
__sbr_cell_3_256:
    mov esi, DWORD PTR [rbp-48]
__sbr_cell_3_256_end:
__sbr_cell_3_257:
    xor eax, eax
__sbr_cell_3_257_end:
__sbr_cell_3_258:
    cmp ecx, esi
__sbr_cell_3_258_end:
__sbr_cell_3_259:
    setl al
__sbr_cell_3_259_end:
__sbr_cell_3_260:
    add eax, ecx
__sbr_cell_3_260_end:
__sbr_cell_3_261:
    movzx edx, BYTE PTR [rdi+rdx*1+0]
__sbr_cell_3_261_end:
__sbr_cell_3_262:
    and cl, 7
__sbr_cell_3_262_end:
__sbr_cell_3_263:
    shl edx, cl
__sbr_cell_3_263_end:
__sbr_cell_3_264:
    shr edx, 7
__sbr_cell_3_264_end:
__sbr_cell_3_265:
    and edx, 1
__sbr_cell_3_265_end:
__sbr_cell_3_266:
    mov DWORD PTR [r14+166308], edx
__sbr_cell_3_266_end:
__sbr_cell_3_267:
    je ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_267_end:
ff_aac_sbr_decode_extension.L43d:
__sbr_cell_3_268:
    movsxd r9, DWORD PTR [r14+477956]
__sbr_cell_3_268_end:
__sbr_cell_3_269:
    test r9, r9
__sbr_cell_3_269_end:
__sbr_cell_3_270:
    jle ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_270_end:
__sbr_cell_3_271:
    mov r8d, r9d
__sbr_cell_3_271_end:
__sbr_cell_3_272:
    and r8d, 3
__sbr_cell_3_272_end:
__sbr_cell_3_273:
    cmp r9d, 4
__sbr_cell_3_273_end:
__sbr_cell_3_274:
    jae ff_aac_sbr_decode_extension.L7de
__sbr_cell_3_274_end:
__sbr_cell_3_275:
    xor r10d, r10d
__sbr_cell_3_275_end:
__sbr_cell_3_276:
    jmp ff_aac_sbr_decode_extension.L898
__sbr_cell_3_276_end:
ff_aac_sbr_decode_extension.L466:
__sbr_cell_3_277:
    mov rdi, QWORD PTR [r12+8]
__sbr_cell_3_277_end:
__sbr_cell_3_278:
    lea rdx, [rip+L_str_21]
__sbr_cell_3_278_end:
__sbr_cell_3_279:
    mov esi, 16
__sbr_cell_3_279_end:
__sbr_cell_3_280:
    mov ecx, r13d
__sbr_cell_3_280_end:
__sbr_cell_3_281:
    xor eax, eax
__sbr_cell_3_281_end:
__sbr_cell_3_282:
    call av_log
__sbr_cell_3_282_end:
ff_aac_sbr_decode_extension.L481:
__sbr_cell_3_283:
    jmp ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_283_end:
ff_aac_sbr_decode_extension.L483:
__sbr_cell_3_284:
    test eax, eax
__sbr_cell_3_284_end:
__sbr_cell_3_285:
    je ff_aac_sbr_decode_extension.L591
__sbr_cell_3_285_end:
ff_aac_sbr_decode_extension.L48b:
__sbr_cell_3_286:
    mov QWORD PTR [r14+166180], 0
__sbr_cell_3_286_end:
__sbr_cell_3_287:
    mov DWORD PTR [r14+166192], 0
__sbr_cell_3_287_end:
ff_aac_sbr_decode_extension.L4a1:
__sbr_cell_3_288:
    mov DWORD PTR [r14+166264], 32
__sbr_cell_3_288_end:
__sbr_cell_3_289:
    mov DWORD PTR [r14+166272], 0
__sbr_cell_3_289_end:
ff_aac_sbr_decode_extension.L4b7:
__sbr_cell_3_290:
    mov DWORD PTR [r14+269672], 4294967295
__sbr_cell_3_290_end:
__sbr_cell_3_291:
    mov DWORD PTR [r14+180904], 4294967295
__sbr_cell_3_291_end:
ff_aac_sbr_decode_extension.L4cd:
__sbr_cell_3_292:
    mov DWORD PTR [r14+166204], 4294967295
__sbr_cell_3_292_end:
__sbr_cell_3_293:
    mov WORD PTR [r14+166208], 65535
__sbr_cell_3_293_end:
ff_aac_sbr_decode_extension.L4e2:
__sbr_cell_3_294:
    sub r15d, DWORD PTR [rbp-88]
__sbr_cell_3_294_end:
__sbr_cell_3_295:
    add r15d, DWORD PTR [rbp-56]
__sbr_cell_3_295_end:
__sbr_cell_3_296:
    mov r12, QWORD PTR [rbp-72]
__sbr_cell_3_296_end:
ff_aac_sbr_decode_extension.L4ee:
__sbr_cell_3_297:
    mov eax, 4
__sbr_cell_3_297_end:
__sbr_cell_3_298:
    sub eax, r15d
__sbr_cell_3_298_end:
__sbr_cell_3_299:
    and eax, 7
__sbr_cell_3_299_end:
__sbr_cell_3_300:
    lea r8d, [r15+rax*1+0]
__sbr_cell_3_300_end:
__sbr_cell_3_301:
    add r8d, 4
__sbr_cell_3_301_end:
__sbr_cell_3_302:
    shr r8d, 3
__sbr_cell_3_302_end:
__sbr_cell_3_303:
    cmp r8d, DWORD PTR [rbp-80]
__sbr_cell_3_303_end:
__sbr_cell_3_304:
    jbe ff_aac_sbr_decode_extension.L57e
__sbr_cell_3_304_end:
ff_aac_sbr_decode_extension.L50b:
__sbr_cell_3_305:
    mov rdi, QWORD PTR [r12+8]
__sbr_cell_3_305_end:
__sbr_cell_3_306:
    lea rdx, [rip+L_str]
__sbr_cell_3_306_end:
__sbr_cell_3_307:
    mov esi, 16
__sbr_cell_3_307_end:
__sbr_cell_3_308:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_3_308_end:
__sbr_cell_3_309:
    xor eax, eax
__sbr_cell_3_309_end:
__sbr_cell_3_310:
    call av_log
__sbr_cell_3_310_end:
ff_aac_sbr_decode_extension.L527:
__sbr_cell_3_311:
    mov QWORD PTR [r14+166180], 0
__sbr_cell_3_311_end:
__sbr_cell_3_312:
    mov DWORD PTR [r14+166192], 0
__sbr_cell_3_312_end:
ff_aac_sbr_decode_extension.L53d:
__sbr_cell_3_313:
    mov DWORD PTR [r14+166264], 32
__sbr_cell_3_313_end:
__sbr_cell_3_314:
    mov DWORD PTR [r14+166272], 0
__sbr_cell_3_314_end:
ff_aac_sbr_decode_extension.L553:
__sbr_cell_3_315:
    mov DWORD PTR [r14+269672], 4294967295
__sbr_cell_3_315_end:
__sbr_cell_3_316:
    mov DWORD PTR [r14+180904], 4294967295
__sbr_cell_3_316_end:
ff_aac_sbr_decode_extension.L569:
__sbr_cell_3_317:
    mov DWORD PTR [r14+166204], 4294967295
__sbr_cell_3_317_end:
__sbr_cell_3_318:
    mov WORD PTR [r14+166208], 65535
__sbr_cell_3_318_end:
ff_aac_sbr_decode_extension.L57e:
__sbr_cell_3_319:
    mov rax, QWORD PTR [rbp-80]
__sbr_cell_3_319_end:
__sbr_cell_3_320:
    add rsp, 56
__sbr_cell_3_320_end:
__sbr_cell_3_321:
    pop rbx
__sbr_cell_3_321_end:
__sbr_cell_3_322:
    pop r12
__sbr_cell_3_322_end:
__sbr_cell_3_323:
    pop r13
__sbr_cell_3_323_end:
__sbr_cell_3_324:
    pop r14
__sbr_cell_3_324_end:
__sbr_cell_3_325:
    pop r15
__sbr_cell_3_325_end:
__sbr_cell_3_326:
    pop rbp
__sbr_cell_3_326_end:
ff_aac_sbr_decode_extension.done:
__sbr_cell_3_327:
    ret
__sbr_cell_3_327_end:
ff_aac_sbr_decode_extension.L591:
__sbr_cell_3_328:
    mov eax, DWORD PTR [r14+255080]
__sbr_cell_3_328_end:
__sbr_cell_3_329:
    cmp rax, 9
__sbr_cell_3_329_end:
__sbr_cell_3_330:
    jae ff_aac_sbr_decode_extension.Lcf6
__sbr_cell_3_330_end:
ff_aac_sbr_decode_extension.L5a2:
__sbr_cell_3_331:
    mov rdx, r13
__sbr_cell_3_331_end:
__sbr_cell_3_332:
    lea rbx, [r14+255072]
__sbr_cell_3_332_end:
__sbr_cell_3_333:
    movzx ecx, BYTE PTR [r14+rax*1+255084]
__sbr_cell_3_333_end:
__sbr_cell_3_334:
    mov BYTE PTR [r14+255084], cl
__sbr_cell_3_334_end:
__sbr_cell_3_335:
    movzx ecx, BYTE PTR [r14+rax*1+343804]
__sbr_cell_3_335_end:
__sbr_cell_3_336:
    mov BYTE PTR [r14+343813], cl
__sbr_cell_3_336_end:
ff_aac_sbr_decode_extension.L5cc:
__sbr_cell_3_337:
    xor ecx, ecx
__sbr_cell_3_337_end:
__sbr_cell_3_338:
    cmp DWORD PTR [r14+269672], eax
__sbr_cell_3_338_end:
__sbr_cell_3_339:
    setne cl
__sbr_cell_3_339_end:
__sbr_cell_3_340:
    neg ecx
__sbr_cell_3_340_end:
__sbr_cell_3_341:
    mov DWORD PTR [r14+269668], ecx
__sbr_cell_3_341_end:
ff_aac_sbr_decode_extension.L5e1:
__sbr_cell_3_342:
    mov rax, QWORD PTR [r14+166317]
__sbr_cell_3_342_end:
__sbr_cell_3_343:
    mov QWORD PTR [r14+255085], rax
__sbr_cell_3_343_end:
__sbr_cell_3_344:
    mov rax, QWORD PTR [r14+255036]
__sbr_cell_3_344_end:
__sbr_cell_3_345:
    mov QWORD PTR [r14+343804], rax
__sbr_cell_3_345_end:
ff_aac_sbr_decode_extension.L5fd:
__sbr_cell_3_346:
    movzx eax, BYTE PTR [r14+255044]
__sbr_cell_3_346_end:
__sbr_cell_3_347:
    mov BYTE PTR [r14+343812], al
__sbr_cell_3_347_end:
__sbr_cell_3_348:
    movzx eax, WORD PTR [r14+255046]
__sbr_cell_3_348_end:
ff_aac_sbr_decode_extension.L614:
__sbr_cell_3_349:
    mov WORD PTR [r14+343814], ax
__sbr_cell_3_349_end:
__sbr_cell_3_350:
    movzx eax, BYTE PTR [r14+255048]
__sbr_cell_3_350_end:
__sbr_cell_3_351:
    mov BYTE PTR [r14+343816], al
__sbr_cell_3_351_end:
ff_aac_sbr_decode_extension.L62b:
__sbr_cell_3_352:
    mov eax, DWORD PTR [r14+166312]
__sbr_cell_3_352_end:
__sbr_cell_3_353:
    mov DWORD PTR [r14+255080], eax
__sbr_cell_3_353_end:
__sbr_cell_3_354:
    mov eax, DWORD PTR [r14+166404]
__sbr_cell_3_354_end:
__sbr_cell_3_355:
    mov DWORD PTR [r14+255172], eax
__sbr_cell_3_355_end:
ff_aac_sbr_decode_extension.L647:
__sbr_cell_3_356:
    mov eax, DWORD PTR [r14+166328]
__sbr_cell_3_356_end:
__sbr_cell_3_357:
    mov DWORD PTR [r14+255096], eax
__sbr_cell_3_357_end:
__sbr_cell_3_358:
    mov eax, DWORD PTR [r14+166304]
__sbr_cell_3_358_end:
__sbr_cell_3_359:
    mov DWORD PTR [r14+255072], eax
__sbr_cell_3_359_end:
ff_aac_sbr_decode_extension.L663:
__sbr_cell_3_360:
    mov eax, DWORD PTR [r14+180904]
__sbr_cell_3_360_end:
__sbr_cell_3_361:
    mov DWORD PTR [r14+269672], eax
__sbr_cell_3_361_end:
__sbr_cell_3_362:
    mov edi, DWORD PTR [r14+166192]
__sbr_cell_3_362_end:
__sbr_cell_3_363:
    lea r13, [rbp-64]
__sbr_cell_3_363_end:
__sbr_cell_3_364:
    mov rsi, r13
__sbr_cell_3_364_end:
__sbr_cell_3_365:
    xor ecx, ecx
__sbr_cell_3_365_end:
__sbr_cell_3_366:
    call read_sbr_dtdf
__sbr_cell_3_366_end:
ff_aac_sbr_decode_extension.L686:
__sbr_cell_3_367:
    mov edi, DWORD PTR [r14+166192]
__sbr_cell_3_367_end:
__sbr_cell_3_368:
    mov rsi, r13
__sbr_cell_3_368_end:
__sbr_cell_3_369:
    mov rdx, rbx
__sbr_cell_3_369_end:
__sbr_cell_3_370:
    xor ecx, ecx
__sbr_cell_3_370_end:
__sbr_cell_3_371:
    call read_sbr_dtdf
__sbr_cell_3_371_end:
ff_aac_sbr_decode_extension.L69a:
__sbr_cell_3_372:
    lea rbx, [r14+166176]
__sbr_cell_3_372_end:
__sbr_cell_3_373:
    mov rdi, rbx
__sbr_cell_3_373_end:
__sbr_cell_3_374:
    mov rsi, r13
__sbr_cell_3_374_end:
__sbr_cell_3_375:
    lea rdx, [r14+166304]
__sbr_cell_3_375_end:
__sbr_cell_3_376:
    call read_sbr_invf
__sbr_cell_3_376_end:
ff_aac_sbr_decode_extension.L6b3:
__sbr_cell_3_377:
    movzx eax, BYTE PTR [r14+255115]
__sbr_cell_3_377_end:
__sbr_cell_3_378:
    mov BYTE PTR [r14+255120], al
__sbr_cell_3_378_end:
__sbr_cell_3_379:
    mov eax, DWORD PTR [r14+255111]
__sbr_cell_3_379_end:
__sbr_cell_3_380:
    mov DWORD PTR [r14+255116], eax
__sbr_cell_3_380_end:
ff_aac_sbr_decode_extension.L6d0:
__sbr_cell_3_381:
    mov eax, DWORD PTR [r14+166343]
__sbr_cell_3_381_end:
__sbr_cell_3_382:
    mov DWORD PTR [r14+255111], eax
__sbr_cell_3_382_end:
__sbr_cell_3_383:
    movzx eax, BYTE PTR [r14+166347]
__sbr_cell_3_383_end:
__sbr_cell_3_384:
    mov BYTE PTR [r14+255115], al
__sbr_cell_3_384_end:
ff_aac_sbr_decode_extension.L6ed:
__sbr_cell_3_385:
    mov rdi, r12
__sbr_cell_3_385_end:
__sbr_cell_3_386:
    mov rsi, rbx
__sbr_cell_3_386_end:
__sbr_cell_3_387:
    mov rdx, r13
__sbr_cell_3_387_end:
__sbr_cell_3_388:
    lea rbx, [r14+166304]
__sbr_cell_3_388_end:
__sbr_cell_3_389:
    mov rcx, rbx
__sbr_cell_3_389_end:
__sbr_cell_3_390:
    xor r8d, r8d
__sbr_cell_3_390_end:
__sbr_cell_3_391:
    call read_sbr_envelope
__sbr_cell_3_391_end:
ff_aac_sbr_decode_extension.L708:
__sbr_cell_3_392:
    test eax, eax
__sbr_cell_3_392_end:
__sbr_cell_3_393:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_393_end:
__sbr_cell_3_394:
    lea rdx, [rbp-64]
__sbr_cell_3_394_end:
__sbr_cell_3_395:
    mov rdi, r12
__sbr_cell_3_395_end:
__sbr_cell_3_396:
    lea rsi, [r14+166176]
__sbr_cell_3_396_end:
__sbr_cell_3_397:
    mov rcx, rbx
__sbr_cell_3_397_end:
__sbr_cell_3_398:
    xor r8d, r8d
__sbr_cell_3_398_end:
__sbr_cell_3_399:
    call read_sbr_noise
__sbr_cell_3_399_end:
ff_aac_sbr_decode_extension.L729:
__sbr_cell_3_400:
    test eax, eax
__sbr_cell_3_400_end:
__sbr_cell_3_401:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_401_end:
__sbr_cell_3_402:
    lea rdx, [rbp-64]
__sbr_cell_3_402_end:
__sbr_cell_3_403:
    mov rdi, r12
__sbr_cell_3_403_end:
__sbr_cell_3_404:
    lea rsi, [r14+166176]
__sbr_cell_3_404_end:
__sbr_cell_3_405:
    lea rcx, [r14+255072]
__sbr_cell_3_405_end:
__sbr_cell_3_406:
    mov r8d, 1
__sbr_cell_3_406_end:
__sbr_cell_3_407:
    call read_sbr_envelope
__sbr_cell_3_407_end:
ff_aac_sbr_decode_extension.L751:
__sbr_cell_3_408:
    test eax, eax
__sbr_cell_3_408_end:
__sbr_cell_3_409:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_409_end:
__sbr_cell_3_410:
    lea rdx, [rbp-64]
__sbr_cell_3_410_end:
__sbr_cell_3_411:
    mov rdi, r12
__sbr_cell_3_411_end:
__sbr_cell_3_412:
    lea rsi, [r14+166176]
__sbr_cell_3_412_end:
__sbr_cell_3_413:
    lea rcx, [r14+255072]
__sbr_cell_3_413_end:
ff_aac_sbr_decode_extension.L76e:
__sbr_cell_3_414:
    mov r8d, 1
__sbr_cell_3_414_end:
__sbr_cell_3_415:
    call read_sbr_noise
__sbr_cell_3_415_end:
ff_aac_sbr_decode_extension.L779:
__sbr_cell_3_416:
    test eax, eax
__sbr_cell_3_416_end:
__sbr_cell_3_417:
    js ff_aac_sbr_decode_extension.L48b
__sbr_cell_3_417_end:
ff_aac_sbr_decode_extension.L781:
__sbr_cell_3_418:
    mov ecx, DWORD PTR [rbp-56]
__sbr_cell_3_418_end:
__sbr_cell_3_419:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_3_419_end:
__sbr_cell_3_420:
    mov eax, ecx
__sbr_cell_3_420_end:
__sbr_cell_3_421:
    shr eax, 3
__sbr_cell_3_421_end:
__sbr_cell_3_422:
    mov esi, DWORD PTR [rbp-48]
__sbr_cell_3_422_end:
__sbr_cell_3_423:
    xor edx, edx
__sbr_cell_3_423_end:
__sbr_cell_3_424:
    cmp ecx, esi
__sbr_cell_3_424_end:
__sbr_cell_3_425:
    setl dl
__sbr_cell_3_425_end:
__sbr_cell_3_426:
    add edx, ecx
__sbr_cell_3_426_end:
__sbr_cell_3_427:
    movzx eax, BYTE PTR [rdi+rax*1+0]
__sbr_cell_3_427_end:
__sbr_cell_3_428:
    and cl, 7
__sbr_cell_3_428_end:
__sbr_cell_3_429:
    shl eax, cl
__sbr_cell_3_429_end:
__sbr_cell_3_430:
    shr eax, 7
__sbr_cell_3_430_end:
__sbr_cell_3_431:
    and eax, 1
__sbr_cell_3_431_end:
__sbr_cell_3_432:
    mov DWORD PTR [r14+166308], eax
__sbr_cell_3_432_end:
__sbr_cell_3_433:
    je ff_aac_sbr_decode_extension.L9d4
__sbr_cell_3_433_end:
ff_aac_sbr_decode_extension.L7b5:
__sbr_cell_3_434:
    movsxd r9, DWORD PTR [r14+477956]
__sbr_cell_3_434_end:
__sbr_cell_3_435:
    test r9, r9
__sbr_cell_3_435_end:
__sbr_cell_3_436:
    jle ff_aac_sbr_decode_extension.L9d4
__sbr_cell_3_436_end:
__sbr_cell_3_437:
    mov r8d, r9d
__sbr_cell_3_437_end:
__sbr_cell_3_438:
    and r8d, 3
__sbr_cell_3_438_end:
__sbr_cell_3_439:
    cmp r9d, 4
__sbr_cell_3_439_end:
__sbr_cell_3_440:
    jae ff_aac_sbr_decode_extension.L8e2
__sbr_cell_3_440_end:
__sbr_cell_3_441:
    xor r10d, r10d
__sbr_cell_3_441_end:
__sbr_cell_3_442:
    jmp ff_aac_sbr_decode_extension.L998
__sbr_cell_3_442_end:
ff_aac_sbr_decode_extension.L7de:
__sbr_cell_3_443:
    and r9d, 2147483644
__sbr_cell_3_443_end:
__sbr_cell_3_444:
    xor r10d, r10d
__sbr_cell_3_444_end:
ff_aac_sbr_decode_extension.L7e8:
__sbr_cell_3_445:
    mov ecx, eax
__sbr_cell_3_445_end:
__sbr_cell_3_446:
    shr ecx, 3
__sbr_cell_3_446_end:
__sbr_cell_3_447:
    xor edx, edx
__sbr_cell_3_447_end:
__sbr_cell_3_448:
    cmp eax, esi
__sbr_cell_3_448_end:
__sbr_cell_3_449:
    setl dl
__sbr_cell_3_449_end:
__sbr_cell_3_450:
    add edx, eax
__sbr_cell_3_450_end:
__sbr_cell_3_451:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_451_end:
__sbr_cell_3_452:
    and al, 7
__sbr_cell_3_452_end:
__sbr_cell_3_453:
    mov ecx, eax
__sbr_cell_3_453_end:
__sbr_cell_3_454:
    shl r11d, cl
__sbr_cell_3_454_end:
__sbr_cell_3_455:
    shr r11b, 7
__sbr_cell_3_455_end:
__sbr_cell_3_456:
    mov BYTE PTR [r14+r10*1+166353], r11b
__sbr_cell_3_456_end:
ff_aac_sbr_decode_extension.L80e:
__sbr_cell_3_457:
    mov ecx, edx
__sbr_cell_3_457_end:
__sbr_cell_3_458:
    shr ecx, 3
__sbr_cell_3_458_end:
__sbr_cell_3_459:
    xor eax, eax
__sbr_cell_3_459_end:
__sbr_cell_3_460:
    cmp edx, esi
__sbr_cell_3_460_end:
__sbr_cell_3_461:
    setl al
__sbr_cell_3_461_end:
__sbr_cell_3_462:
    add eax, edx
__sbr_cell_3_462_end:
__sbr_cell_3_463:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_463_end:
__sbr_cell_3_464:
    and dl, 7
__sbr_cell_3_464_end:
__sbr_cell_3_465:
    mov ecx, edx
__sbr_cell_3_465_end:
__sbr_cell_3_466:
    shl r11d, cl
__sbr_cell_3_466_end:
__sbr_cell_3_467:
    shr r11b, 7
__sbr_cell_3_467_end:
__sbr_cell_3_468:
    mov BYTE PTR [r14+r10*1+166354], r11b
__sbr_cell_3_468_end:
ff_aac_sbr_decode_extension.L835:
__sbr_cell_3_469:
    mov ecx, eax
__sbr_cell_3_469_end:
__sbr_cell_3_470:
    shr ecx, 3
__sbr_cell_3_470_end:
__sbr_cell_3_471:
    xor edx, edx
__sbr_cell_3_471_end:
__sbr_cell_3_472:
    cmp eax, esi
__sbr_cell_3_472_end:
__sbr_cell_3_473:
    setl dl
__sbr_cell_3_473_end:
__sbr_cell_3_474:
    add edx, eax
__sbr_cell_3_474_end:
__sbr_cell_3_475:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_475_end:
__sbr_cell_3_476:
    and al, 7
__sbr_cell_3_476_end:
__sbr_cell_3_477:
    mov ecx, eax
__sbr_cell_3_477_end:
__sbr_cell_3_478:
    shl r11d, cl
__sbr_cell_3_478_end:
__sbr_cell_3_479:
    shr r11b, 7
__sbr_cell_3_479_end:
__sbr_cell_3_480:
    mov BYTE PTR [r14+r10*1+166355], r11b
__sbr_cell_3_480_end:
ff_aac_sbr_decode_extension.L85b:
__sbr_cell_3_481:
    mov ecx, edx
__sbr_cell_3_481_end:
__sbr_cell_3_482:
    shr ecx, 3
__sbr_cell_3_482_end:
__sbr_cell_3_483:
    xor eax, eax
__sbr_cell_3_483_end:
__sbr_cell_3_484:
    cmp edx, esi
__sbr_cell_3_484_end:
__sbr_cell_3_485:
    setl al
__sbr_cell_3_485_end:
__sbr_cell_3_486:
    add eax, edx
__sbr_cell_3_486_end:
__sbr_cell_3_487:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_487_end:
__sbr_cell_3_488:
    and dl, 7
__sbr_cell_3_488_end:
__sbr_cell_3_489:
    mov ecx, edx
__sbr_cell_3_489_end:
__sbr_cell_3_490:
    shl r11d, cl
__sbr_cell_3_490_end:
__sbr_cell_3_491:
    shr r11b, 7
__sbr_cell_3_491_end:
__sbr_cell_3_492:
    mov BYTE PTR [r14+r10*1+166356], r11b
__sbr_cell_3_492_end:
__sbr_cell_3_493:
    add r10, 4
__sbr_cell_3_493_end:
__sbr_cell_3_494:
    cmp r9, r10
__sbr_cell_3_494_end:
__sbr_cell_3_495:
    jne ff_aac_sbr_decode_extension.L7e8
__sbr_cell_3_495_end:
__sbr_cell_3_496:
    test r8, r8
__sbr_cell_3_496_end:
__sbr_cell_3_497:
    je ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_497_end:
ff_aac_sbr_decode_extension.L898:
__sbr_cell_3_498:
    lea rdx, [r10+r14*1+0]
__sbr_cell_3_498_end:
__sbr_cell_3_499:
    add rdx, 166353
__sbr_cell_3_499_end:
__sbr_cell_3_500:
    xor r9d, r9d
__sbr_cell_3_500_end:
__sbr_cell_3_501:
    .nops 1
__sbr_cell_3_501_end:
ff_aac_sbr_decode_extension.L8b0:
__sbr_cell_3_502:
    mov ecx, eax
__sbr_cell_3_502_end:
__sbr_cell_3_503:
    mov r10d, eax
__sbr_cell_3_503_end:
__sbr_cell_3_504:
    shr r10d, 3
__sbr_cell_3_504_end:
__sbr_cell_3_505:
    xor eax, eax
__sbr_cell_3_505_end:
__sbr_cell_3_506:
    cmp ecx, esi
__sbr_cell_3_506_end:
__sbr_cell_3_507:
    setl al
__sbr_cell_3_507_end:
__sbr_cell_3_508:
    add eax, ecx
__sbr_cell_3_508_end:
__sbr_cell_3_509:
    movzx r10d, BYTE PTR [rdi+r10*1+0]
__sbr_cell_3_509_end:
__sbr_cell_3_510:
    and cl, 7
__sbr_cell_3_510_end:
__sbr_cell_3_511:
    shl r10d, cl
__sbr_cell_3_511_end:
__sbr_cell_3_512:
    shr r10b, 7
__sbr_cell_3_512_end:
__sbr_cell_3_513:
    mov BYTE PTR [rdx+r9*1+0], r10b
__sbr_cell_3_513_end:
__sbr_cell_3_514:
    inc r9
__sbr_cell_3_514_end:
__sbr_cell_3_515:
    cmp r8, r9
__sbr_cell_3_515_end:
__sbr_cell_3_516:
    jne ff_aac_sbr_decode_extension.L8b0
__sbr_cell_3_516_end:
__sbr_cell_3_517:
    jmp ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_517_end:
ff_aac_sbr_decode_extension.L8e2:
__sbr_cell_3_518:
    and r9d, 2147483644
__sbr_cell_3_518_end:
__sbr_cell_3_519:
    xor r10d, r10d
__sbr_cell_3_519_end:
ff_aac_sbr_decode_extension.L8ec:
__sbr_cell_3_520:
    mov ecx, edx
__sbr_cell_3_520_end:
__sbr_cell_3_521:
    shr ecx, 3
__sbr_cell_3_521_end:
__sbr_cell_3_522:
    xor eax, eax
__sbr_cell_3_522_end:
__sbr_cell_3_523:
    cmp edx, esi
__sbr_cell_3_523_end:
__sbr_cell_3_524:
    setl al
__sbr_cell_3_524_end:
__sbr_cell_3_525:
    add eax, edx
__sbr_cell_3_525_end:
__sbr_cell_3_526:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_526_end:
__sbr_cell_3_527:
    and dl, 7
__sbr_cell_3_527_end:
__sbr_cell_3_528:
    mov ecx, edx
__sbr_cell_3_528_end:
__sbr_cell_3_529:
    shl r11d, cl
__sbr_cell_3_529_end:
__sbr_cell_3_530:
    shr r11b, 7
__sbr_cell_3_530_end:
__sbr_cell_3_531:
    mov BYTE PTR [r14+r10*1+166353], r11b
__sbr_cell_3_531_end:
ff_aac_sbr_decode_extension.L913:
__sbr_cell_3_532:
    mov ecx, eax
__sbr_cell_3_532_end:
__sbr_cell_3_533:
    shr ecx, 3
__sbr_cell_3_533_end:
__sbr_cell_3_534:
    xor edx, edx
__sbr_cell_3_534_end:
__sbr_cell_3_535:
    cmp eax, esi
__sbr_cell_3_535_end:
__sbr_cell_3_536:
    setl dl
__sbr_cell_3_536_end:
__sbr_cell_3_537:
    add edx, eax
__sbr_cell_3_537_end:
__sbr_cell_3_538:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_538_end:
__sbr_cell_3_539:
    and al, 7
__sbr_cell_3_539_end:
__sbr_cell_3_540:
    mov ecx, eax
__sbr_cell_3_540_end:
__sbr_cell_3_541:
    shl r11d, cl
__sbr_cell_3_541_end:
__sbr_cell_3_542:
    shr r11b, 7
__sbr_cell_3_542_end:
__sbr_cell_3_543:
    mov BYTE PTR [r14+r10*1+166354], r11b
__sbr_cell_3_543_end:
ff_aac_sbr_decode_extension.L939:
__sbr_cell_3_544:
    mov ecx, edx
__sbr_cell_3_544_end:
__sbr_cell_3_545:
    shr ecx, 3
__sbr_cell_3_545_end:
__sbr_cell_3_546:
    xor eax, eax
__sbr_cell_3_546_end:
__sbr_cell_3_547:
    cmp edx, esi
__sbr_cell_3_547_end:
__sbr_cell_3_548:
    setl al
__sbr_cell_3_548_end:
__sbr_cell_3_549:
    add eax, edx
__sbr_cell_3_549_end:
__sbr_cell_3_550:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_550_end:
__sbr_cell_3_551:
    and dl, 7
__sbr_cell_3_551_end:
__sbr_cell_3_552:
    mov ecx, edx
__sbr_cell_3_552_end:
__sbr_cell_3_553:
    shl r11d, cl
__sbr_cell_3_553_end:
__sbr_cell_3_554:
    shr r11b, 7
__sbr_cell_3_554_end:
__sbr_cell_3_555:
    mov BYTE PTR [r14+r10*1+166355], r11b
__sbr_cell_3_555_end:
ff_aac_sbr_decode_extension.L960:
__sbr_cell_3_556:
    mov ecx, eax
__sbr_cell_3_556_end:
__sbr_cell_3_557:
    shr ecx, 3
__sbr_cell_3_557_end:
__sbr_cell_3_558:
    xor edx, edx
__sbr_cell_3_558_end:
__sbr_cell_3_559:
    cmp eax, esi
__sbr_cell_3_559_end:
__sbr_cell_3_560:
    setl dl
__sbr_cell_3_560_end:
__sbr_cell_3_561:
    add edx, eax
__sbr_cell_3_561_end:
__sbr_cell_3_562:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_562_end:
__sbr_cell_3_563:
    and al, 7
__sbr_cell_3_563_end:
__sbr_cell_3_564:
    mov ecx, eax
__sbr_cell_3_564_end:
__sbr_cell_3_565:
    shl r11d, cl
__sbr_cell_3_565_end:
__sbr_cell_3_566:
    shr r11b, 7
__sbr_cell_3_566_end:
__sbr_cell_3_567:
    mov BYTE PTR [r14+r10*1+166356], r11b
__sbr_cell_3_567_end:
__sbr_cell_3_568:
    add r10, 4
__sbr_cell_3_568_end:
__sbr_cell_3_569:
    cmp r9, r10
__sbr_cell_3_569_end:
__sbr_cell_3_570:
    jne ff_aac_sbr_decode_extension.L8ec
__sbr_cell_3_570_end:
__sbr_cell_3_571:
    test r8, r8
__sbr_cell_3_571_end:
__sbr_cell_3_572:
    je ff_aac_sbr_decode_extension.L9d4
__sbr_cell_3_572_end:
ff_aac_sbr_decode_extension.L998:
__sbr_cell_3_573:
    lea rax, [r10+r14*1+0]
__sbr_cell_3_573_end:
__sbr_cell_3_574:
    add rax, 166353
__sbr_cell_3_574_end:
__sbr_cell_3_575:
    xor r9d, r9d
__sbr_cell_3_575_end:
__sbr_cell_3_576:
    mov ecx, edx
__sbr_cell_3_576_end:
ff_aac_sbr_decode_extension.L9a7:
__sbr_cell_3_577:
    mov r10d, ecx
__sbr_cell_3_577_end:
__sbr_cell_3_578:
    shr r10d, 3
__sbr_cell_3_578_end:
__sbr_cell_3_579:
    xor edx, edx
__sbr_cell_3_579_end:
__sbr_cell_3_580:
    cmp ecx, esi
__sbr_cell_3_580_end:
__sbr_cell_3_581:
    setl dl
__sbr_cell_3_581_end:
__sbr_cell_3_582:
    add edx, ecx
__sbr_cell_3_582_end:
__sbr_cell_3_583:
    movzx r10d, BYTE PTR [rdi+r10*1+0]
__sbr_cell_3_583_end:
__sbr_cell_3_584:
    and cl, 7
__sbr_cell_3_584_end:
__sbr_cell_3_585:
    shl r10d, cl
__sbr_cell_3_585_end:
__sbr_cell_3_586:
    shr r10b, 7
__sbr_cell_3_586_end:
__sbr_cell_3_587:
    mov BYTE PTR [rax+r9*1+0], r10b
__sbr_cell_3_587_end:
__sbr_cell_3_588:
    inc r9
__sbr_cell_3_588_end:
__sbr_cell_3_589:
    mov ecx, edx
__sbr_cell_3_589_end:
__sbr_cell_3_590:
    cmp r8, r9
__sbr_cell_3_590_end:
__sbr_cell_3_591:
    jne ff_aac_sbr_decode_extension.L9a7
__sbr_cell_3_591_end:
ff_aac_sbr_decode_extension.L9d4:
__sbr_cell_3_592:
    mov ecx, edx
__sbr_cell_3_592_end:
__sbr_cell_3_593:
    shr ecx, 3
__sbr_cell_3_593_end:
__sbr_cell_3_594:
    xor eax, eax
__sbr_cell_3_594_end:
__sbr_cell_3_595:
    cmp edx, esi
__sbr_cell_3_595_end:
__sbr_cell_3_596:
    setl al
__sbr_cell_3_596_end:
__sbr_cell_3_597:
    add eax, edx
__sbr_cell_3_597_end:
__sbr_cell_3_598:
    movzx r8d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_598_end:
__sbr_cell_3_599:
    and dl, 7
__sbr_cell_3_599_end:
__sbr_cell_3_600:
    mov ecx, edx
__sbr_cell_3_600_end:
__sbr_cell_3_601:
    shl r8d, cl
__sbr_cell_3_601_end:
__sbr_cell_3_602:
    shr r8d, 7
__sbr_cell_3_602_end:
__sbr_cell_3_603:
    and r8d, 1
__sbr_cell_3_603_end:
__sbr_cell_3_604:
    mov DWORD PTR [r14+255076], r8d
__sbr_cell_3_604_end:
__sbr_cell_3_605:
    je ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_605_end:
ff_aac_sbr_decode_extension.La04:
__sbr_cell_3_606:
    movsxd r9, DWORD PTR [r14+477956]
__sbr_cell_3_606_end:
__sbr_cell_3_607:
    test r9, r9
__sbr_cell_3_607_end:
__sbr_cell_3_608:
    jle ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_608_end:
__sbr_cell_3_609:
    mov r8d, r9d
__sbr_cell_3_609_end:
__sbr_cell_3_610:
    and r8d, 3
__sbr_cell_3_610_end:
__sbr_cell_3_611:
    cmp r9d, 4
__sbr_cell_3_611_end:
__sbr_cell_3_612:
    jae ff_aac_sbr_decode_extension.La29
__sbr_cell_3_612_end:
__sbr_cell_3_613:
    xor r10d, r10d
__sbr_cell_3_613_end:
__sbr_cell_3_614:
    jmp ff_aac_sbr_decode_extension.Ladf
__sbr_cell_3_614_end:
ff_aac_sbr_decode_extension.La29:
__sbr_cell_3_615:
    and r9d, 2147483644
__sbr_cell_3_615_end:
__sbr_cell_3_616:
    xor r10d, r10d
__sbr_cell_3_616_end:
ff_aac_sbr_decode_extension.La33:
__sbr_cell_3_617:
    mov ecx, eax
__sbr_cell_3_617_end:
__sbr_cell_3_618:
    shr ecx, 3
__sbr_cell_3_618_end:
__sbr_cell_3_619:
    xor edx, edx
__sbr_cell_3_619_end:
__sbr_cell_3_620:
    cmp eax, esi
__sbr_cell_3_620_end:
__sbr_cell_3_621:
    setl dl
__sbr_cell_3_621_end:
__sbr_cell_3_622:
    add edx, eax
__sbr_cell_3_622_end:
__sbr_cell_3_623:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_623_end:
__sbr_cell_3_624:
    and al, 7
__sbr_cell_3_624_end:
__sbr_cell_3_625:
    mov ecx, eax
__sbr_cell_3_625_end:
__sbr_cell_3_626:
    shl r11d, cl
__sbr_cell_3_626_end:
__sbr_cell_3_627:
    shr r11b, 7
__sbr_cell_3_627_end:
__sbr_cell_3_628:
    mov BYTE PTR [r14+r10*1+255121], r11b
__sbr_cell_3_628_end:
ff_aac_sbr_decode_extension.La59:
__sbr_cell_3_629:
    mov ecx, edx
__sbr_cell_3_629_end:
__sbr_cell_3_630:
    shr ecx, 3
__sbr_cell_3_630_end:
__sbr_cell_3_631:
    xor eax, eax
__sbr_cell_3_631_end:
__sbr_cell_3_632:
    cmp edx, esi
__sbr_cell_3_632_end:
__sbr_cell_3_633:
    setl al
__sbr_cell_3_633_end:
__sbr_cell_3_634:
    add eax, edx
__sbr_cell_3_634_end:
__sbr_cell_3_635:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_635_end:
__sbr_cell_3_636:
    and dl, 7
__sbr_cell_3_636_end:
__sbr_cell_3_637:
    mov ecx, edx
__sbr_cell_3_637_end:
__sbr_cell_3_638:
    shl r11d, cl
__sbr_cell_3_638_end:
__sbr_cell_3_639:
    shr r11b, 7
__sbr_cell_3_639_end:
__sbr_cell_3_640:
    mov BYTE PTR [r14+r10*1+255122], r11b
__sbr_cell_3_640_end:
ff_aac_sbr_decode_extension.La80:
__sbr_cell_3_641:
    mov ecx, eax
__sbr_cell_3_641_end:
__sbr_cell_3_642:
    shr ecx, 3
__sbr_cell_3_642_end:
__sbr_cell_3_643:
    xor edx, edx
__sbr_cell_3_643_end:
__sbr_cell_3_644:
    cmp eax, esi
__sbr_cell_3_644_end:
__sbr_cell_3_645:
    setl dl
__sbr_cell_3_645_end:
__sbr_cell_3_646:
    add edx, eax
__sbr_cell_3_646_end:
__sbr_cell_3_647:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_647_end:
__sbr_cell_3_648:
    and al, 7
__sbr_cell_3_648_end:
__sbr_cell_3_649:
    mov ecx, eax
__sbr_cell_3_649_end:
__sbr_cell_3_650:
    shl r11d, cl
__sbr_cell_3_650_end:
__sbr_cell_3_651:
    shr r11b, 7
__sbr_cell_3_651_end:
__sbr_cell_3_652:
    mov BYTE PTR [r14+r10*1+255123], r11b
__sbr_cell_3_652_end:
ff_aac_sbr_decode_extension.Laa6:
__sbr_cell_3_653:
    mov ecx, edx
__sbr_cell_3_653_end:
__sbr_cell_3_654:
    shr ecx, 3
__sbr_cell_3_654_end:
__sbr_cell_3_655:
    xor eax, eax
__sbr_cell_3_655_end:
__sbr_cell_3_656:
    cmp edx, esi
__sbr_cell_3_656_end:
__sbr_cell_3_657:
    setl al
__sbr_cell_3_657_end:
__sbr_cell_3_658:
    add eax, edx
__sbr_cell_3_658_end:
__sbr_cell_3_659:
    movzx r11d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_659_end:
__sbr_cell_3_660:
    and dl, 7
__sbr_cell_3_660_end:
__sbr_cell_3_661:
    mov ecx, edx
__sbr_cell_3_661_end:
__sbr_cell_3_662:
    shl r11d, cl
__sbr_cell_3_662_end:
__sbr_cell_3_663:
    shr r11b, 7
__sbr_cell_3_663_end:
__sbr_cell_3_664:
    mov BYTE PTR [r14+r10*1+255124], r11b
__sbr_cell_3_664_end:
__sbr_cell_3_665:
    add r10, 4
__sbr_cell_3_665_end:
__sbr_cell_3_666:
    cmp r9, r10
__sbr_cell_3_666_end:
__sbr_cell_3_667:
    jne ff_aac_sbr_decode_extension.La33
__sbr_cell_3_667_end:
__sbr_cell_3_668:
    test r8, r8
__sbr_cell_3_668_end:
__sbr_cell_3_669:
    je ff_aac_sbr_decode_extension.Lb1a
__sbr_cell_3_669_end:
ff_aac_sbr_decode_extension.Ladf:
__sbr_cell_3_670:
    lea rdx, [r10+r14*1+0]
__sbr_cell_3_670_end:
__sbr_cell_3_671:
    add rdx, 255121
__sbr_cell_3_671_end:
__sbr_cell_3_672:
    xor r9d, r9d
__sbr_cell_3_672_end:
ff_aac_sbr_decode_extension.Laed:
__sbr_cell_3_673:
    mov ecx, eax
__sbr_cell_3_673_end:
__sbr_cell_3_674:
    mov r10d, eax
__sbr_cell_3_674_end:
__sbr_cell_3_675:
    shr r10d, 3
__sbr_cell_3_675_end:
__sbr_cell_3_676:
    xor eax, eax
__sbr_cell_3_676_end:
__sbr_cell_3_677:
    cmp ecx, esi
__sbr_cell_3_677_end:
__sbr_cell_3_678:
    setl al
__sbr_cell_3_678_end:
__sbr_cell_3_679:
    add eax, ecx
__sbr_cell_3_679_end:
__sbr_cell_3_680:
    movzx r10d, BYTE PTR [rdi+r10*1+0]
__sbr_cell_3_680_end:
__sbr_cell_3_681:
    and cl, 7
__sbr_cell_3_681_end:
__sbr_cell_3_682:
    shl r10d, cl
__sbr_cell_3_682_end:
__sbr_cell_3_683:
    shr r10b, 7
__sbr_cell_3_683_end:
__sbr_cell_3_684:
    mov BYTE PTR [rdx+r9*1+0], r10b
__sbr_cell_3_684_end:
__sbr_cell_3_685:
    inc r9
__sbr_cell_3_685_end:
__sbr_cell_3_686:
    cmp r8, r9
__sbr_cell_3_686_end:
__sbr_cell_3_687:
    jne ff_aac_sbr_decode_extension.Laed
__sbr_cell_3_687_end:
ff_aac_sbr_decode_extension.Lb1a:
__sbr_cell_3_688:
    mov ecx, eax
__sbr_cell_3_688_end:
__sbr_cell_3_689:
    shr ecx, 3
__sbr_cell_3_689_end:
__sbr_cell_3_690:
    xor edx, edx
__sbr_cell_3_690_end:
__sbr_cell_3_691:
    cmp eax, esi
__sbr_cell_3_691_end:
__sbr_cell_3_692:
    setl dl
__sbr_cell_3_692_end:
__sbr_cell_3_693:
    add edx, eax
__sbr_cell_3_693_end:
__sbr_cell_3_694:
    movzx r8d, BYTE PTR [rdi+rcx*1+0]
__sbr_cell_3_694_end:
__sbr_cell_3_695:
    mov DWORD PTR [rbp-56], edx
__sbr_cell_3_695_end:
__sbr_cell_3_696:
    and al, 7
__sbr_cell_3_696_end:
__sbr_cell_3_697:
    mov ecx, eax
__sbr_cell_3_697_end:
__sbr_cell_3_698:
    shl r8d, cl
__sbr_cell_3_698_end:
__sbr_cell_3_699:
    test r8b, r8b
__sbr_cell_3_699_end:
__sbr_cell_3_700:
    jns ff_aac_sbr_decode_extension.L4e2
__sbr_cell_3_700_end:
ff_aac_sbr_decode_extension.Lb40:
__sbr_cell_3_701:
    mov eax, edx
__sbr_cell_3_701_end:
__sbr_cell_3_702:
    shr eax, 3
__sbr_cell_3_702_end:
__sbr_cell_3_703:
    mov eax, DWORD PTR [rdi+rax*1+0]
__sbr_cell_3_703_end:
__sbr_cell_3_704:
    bswap eax
__sbr_cell_3_704_end:
__sbr_cell_3_705:
    mov ecx, edx
__sbr_cell_3_705_end:
__sbr_cell_3_706:
    and cl, 7
__sbr_cell_3_706_end:
__sbr_cell_3_707:
    shl eax, cl
__sbr_cell_3_707_end:
__sbr_cell_3_708:
    shr eax, 28
__sbr_cell_3_708_end:
__sbr_cell_3_709:
    add edx, 4
__sbr_cell_3_709_end:
__sbr_cell_3_710:
    cmp esi, edx
__sbr_cell_3_710_end:
__sbr_cell_3_711:
    cmovb edx, esi
__sbr_cell_3_711_end:
__sbr_cell_3_712:
    mov DWORD PTR [rbp-56], edx
__sbr_cell_3_712_end:
__sbr_cell_3_713:
    cmp eax, 15
__sbr_cell_3_713_end:
__sbr_cell_3_714:
    jne ff_aac_sbr_decode_extension.Lb86
__sbr_cell_3_714_end:
ff_aac_sbr_decode_extension.Lb64:
__sbr_cell_3_715:
    mov eax, edx
__sbr_cell_3_715_end:
__sbr_cell_3_716:
    shr eax, 3
__sbr_cell_3_716_end:
__sbr_cell_3_717:
    mov eax, DWORD PTR [rdi+rax*1+0]
__sbr_cell_3_717_end:
__sbr_cell_3_718:
    bswap eax
__sbr_cell_3_718_end:
__sbr_cell_3_719:
    mov ecx, edx
__sbr_cell_3_719_end:
__sbr_cell_3_720:
    and cl, 7
__sbr_cell_3_720_end:
__sbr_cell_3_721:
    shl eax, cl
__sbr_cell_3_721_end:
__sbr_cell_3_722:
    shr eax, 24
__sbr_cell_3_722_end:
__sbr_cell_3_723:
    add edx, 8
__sbr_cell_3_723_end:
__sbr_cell_3_724:
    cmp esi, edx
__sbr_cell_3_724_end:
__sbr_cell_3_725:
    cmovb edx, esi
__sbr_cell_3_725_end:
__sbr_cell_3_726:
    mov DWORD PTR [rbp-56], edx
__sbr_cell_3_726_end:
__sbr_cell_3_727:
    add eax, 15
__sbr_cell_3_727_end:
ff_aac_sbr_decode_extension.Lb86:
__sbr_cell_3_728:
    shl eax, 3
__sbr_cell_3_728_end:
__sbr_cell_3_729:
    cmp eax, 8
__sbr_cell_3_729_end:
__sbr_cell_3_730:
    jl ff_aac_sbr_decode_extension.Lc1c
__sbr_cell_3_730_end:
__sbr_cell_3_731:
    lea rbx, [r14+343840]
__sbr_cell_3_731_end:
__sbr_cell_3_732:
    mov r13, QWORD PTR [rbp-72]
__sbr_cell_3_732_end:
ff_aac_sbr_decode_extension.Lb9d:
__sbr_cell_3_733:
    lea r12d, [rax-2]
__sbr_cell_3_733_end:
__sbr_cell_3_734:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_3_734_end:
__sbr_cell_3_735:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_3_735_end:
__sbr_cell_3_736:
    mov ecx, edx
__sbr_cell_3_736_end:
__sbr_cell_3_737:
    shr ecx, 3
__sbr_cell_3_737_end:
__sbr_cell_3_738:
    mov r8d, DWORD PTR [rdi+rcx*1+0]
__sbr_cell_3_738_end:
__sbr_cell_3_739:
    bswap r8d
__sbr_cell_3_739_end:
__sbr_cell_3_740:
    mov ecx, edx
__sbr_cell_3_740_end:
__sbr_cell_3_741:
    and cl, 7
__sbr_cell_3_741_end:
__sbr_cell_3_742:
    shl r8d, cl
__sbr_cell_3_742_end:
__sbr_cell_3_743:
    mov esi, DWORD PTR [rbp-48]
__sbr_cell_3_743_end:
__sbr_cell_3_744:
    shr r8d, 30
__sbr_cell_3_744_end:
__sbr_cell_3_745:
    add edx, 2
__sbr_cell_3_745_end:
__sbr_cell_3_746:
    cmp esi, edx
__sbr_cell_3_746_end:
__sbr_cell_3_747:
    cmovb edx, esi
__sbr_cell_3_747_end:
__sbr_cell_3_748:
    mov DWORD PTR [rbp-56], edx
__sbr_cell_3_748_end:
__sbr_cell_3_749:
    cmp r8d, 2
__sbr_cell_3_749_end:
__sbr_cell_3_750:
    jne ff_aac_sbr_decode_extension.Lc41
__sbr_cell_3_750_end:
ff_aac_sbr_decode_extension.Lbd4:
__sbr_cell_3_751:
    cmp DWORD PTR [r13+22528], 0
__sbr_cell_3_751_end:
__sbr_cell_3_752:
    mov rdi, QWORD PTR [r13+8]
__sbr_cell_3_752_end:
__sbr_cell_3_753:
    je ff_aac_sbr_decode_extension.Lcc0
__sbr_cell_3_753_end:
ff_aac_sbr_decode_extension.Lbe6:
__sbr_cell_3_754:
    lea rsi, [rbp-64]
__sbr_cell_3_754_end:
__sbr_cell_3_755:
    mov rdx, rbx
__sbr_cell_3_755_end:
__sbr_cell_3_756:
    mov ecx, r12d
__sbr_cell_3_756_end:
__sbr_cell_3_757:
    call ff_ps_read_data
__sbr_cell_3_757_end:
ff_aac_sbr_decode_extension.Lbf5:
__sbr_cell_3_758:
    sub r12d, eax
__sbr_cell_3_758_end:
__sbr_cell_3_759:
    mov rax, QWORD PTR [r13+8]
__sbr_cell_3_759_end:
__sbr_cell_3_760:
    mov DWORD PTR [rax+688], 28
__sbr_cell_3_760_end:
__sbr_cell_3_761:
    mov DWORD PTR [r13+34896], 1
__sbr_cell_3_761_end:
__sbr_cell_3_762:
    mov eax, r12d
__sbr_cell_3_762_end:
__sbr_cell_3_763:
    cmp r12d, 7
__sbr_cell_3_763_end:
__sbr_cell_3_764:
    jg ff_aac_sbr_decode_extension.Lb9d
__sbr_cell_3_764_end:
__sbr_cell_3_765:
    jmp ff_aac_sbr_decode_extension.Lc1f
__sbr_cell_3_765_end:
ff_aac_sbr_decode_extension.Lc1c:
__sbr_cell_3_766:
    mov r12d, eax
__sbr_cell_3_766_end:
ff_aac_sbr_decode_extension.Lc1f:
__sbr_cell_3_767:
    test r12d, r12d
__sbr_cell_3_767_end:
__sbr_cell_3_768:
    js ff_aac_sbr_decode_extension.Lca0
__sbr_cell_3_768_end:
__sbr_cell_3_769:
    je ff_aac_sbr_decode_extension.L4e2
__sbr_cell_3_769_end:
__sbr_cell_3_770:
    mov eax, DWORD PTR [rbp-48]
__sbr_cell_3_770_end:
__sbr_cell_3_771:
    add r12d, DWORD PTR [rbp-56]
__sbr_cell_3_771_end:
__sbr_cell_3_772:
    cmp eax, r12d
__sbr_cell_3_772_end:
__sbr_cell_3_773:
    cmovb r12d, eax
__sbr_cell_3_773_end:
__sbr_cell_3_774:
    mov DWORD PTR [rbp-56], r12d
__sbr_cell_3_774_end:
__sbr_cell_3_775:
    jmp ff_aac_sbr_decode_extension.L4e2
__sbr_cell_3_775_end:
ff_aac_sbr_decode_extension.Lc41:
__sbr_cell_3_776:
    test r8d, r8d
__sbr_cell_3_776_end:
__sbr_cell_3_777:
    jne ff_aac_sbr_decode_extension.Lc67
__sbr_cell_3_777_end:
__sbr_cell_3_778:
    cmp eax, 18
__sbr_cell_3_778_end:
__sbr_cell_3_779:
    ja ff_aac_sbr_decode_extension.Lc67
__sbr_cell_3_779_end:
ff_aac_sbr_decode_extension.Lc4b:
__sbr_cell_3_780:
    mov eax, edx
__sbr_cell_3_780_end:
__sbr_cell_3_781:
    shr eax, 3
__sbr_cell_3_781_end:
__sbr_cell_3_782:
    mov eax, DWORD PTR [rdi+rax*1+0]
__sbr_cell_3_782_end:
__sbr_cell_3_783:
    bswap eax
__sbr_cell_3_783_end:
__sbr_cell_3_784:
    mov ecx, edx
__sbr_cell_3_784_end:
__sbr_cell_3_785:
    and cl, 7
__sbr_cell_3_785_end:
__sbr_cell_3_786:
    shl eax, cl
__sbr_cell_3_786_end:
__sbr_cell_3_787:
    mov ecx, r12d
__sbr_cell_3_787_end:
__sbr_cell_3_788:
    neg cl
__sbr_cell_3_788_end:
__sbr_cell_3_789:
    shr eax, cl
__sbr_cell_3_789_end:
__sbr_cell_3_790:
    test eax, eax
__sbr_cell_3_790_end:
__sbr_cell_3_791:
    je ff_aac_sbr_decode_extension.Lc83
__sbr_cell_3_791_end:
ff_aac_sbr_decode_extension.Lc67:
__sbr_cell_3_792:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_3_792_end:
__sbr_cell_3_793:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_3_793_end:
__sbr_cell_3_794:
    lea rsi, [rip+L_str_24]
__sbr_cell_3_794_end:
__sbr_cell_3_795:
    xor eax, eax
__sbr_cell_3_795_end:
__sbr_cell_3_796:
    call avpriv_request_sample
__sbr_cell_3_796_end:
ff_aac_sbr_decode_extension.Lc7d:
__sbr_cell_3_797:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_3_797_end:
__sbr_cell_3_798:
    mov esi, DWORD PTR [rbp-48]
__sbr_cell_3_798_end:
ff_aac_sbr_decode_extension.Lc83:
__sbr_cell_3_799:
    mov eax, edx
__sbr_cell_3_799_end:
__sbr_cell_3_800:
    neg eax
__sbr_cell_3_800_end:
__sbr_cell_3_801:
    sub esi, edx
__sbr_cell_3_801_end:
__sbr_cell_3_802:
    cmp r12d, esi
__sbr_cell_3_802_end:
__sbr_cell_3_803:
    cmovl esi, r12d
__sbr_cell_3_803_end:
__sbr_cell_3_804:
    cmp r12d, eax
__sbr_cell_3_804_end:
__sbr_cell_3_805:
    cmovl esi, eax
__sbr_cell_3_805_end:
__sbr_cell_3_806:
    add esi, edx
__sbr_cell_3_806_end:
__sbr_cell_3_807:
    mov DWORD PTR [rbp-56], esi
__sbr_cell_3_807_end:
__sbr_cell_3_808:
    jmp ff_aac_sbr_decode_extension.L4e2
__sbr_cell_3_808_end:
ff_aac_sbr_decode_extension.Lca0:
__sbr_cell_3_809:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_3_809_end:
__sbr_cell_3_810:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_3_810_end:
__sbr_cell_3_811:
    lea rdx, [rip+L_str_22]
__sbr_cell_3_811_end:
__sbr_cell_3_812:
    mov esi, 16
__sbr_cell_3_812_end:
__sbr_cell_3_813:
    xor eax, eax
__sbr_cell_3_813_end:
__sbr_cell_3_814:
    call av_log
__sbr_cell_3_814_end:
ff_aac_sbr_decode_extension.Lcbb:
__sbr_cell_3_815:
    jmp ff_aac_sbr_decode_extension.L4e2
__sbr_cell_3_815_end:
ff_aac_sbr_decode_extension.Lcc0:
__sbr_cell_3_816:
    lea rdx, [rip+L_str_23]
__sbr_cell_3_816_end:
__sbr_cell_3_817:
    mov esi, 16
__sbr_cell_3_817_end:
__sbr_cell_3_818:
    xor eax, eax
__sbr_cell_3_818_end:
__sbr_cell_3_819:
    call av_log
__sbr_cell_3_819_end:
ff_aac_sbr_decode_extension.Lcd3:
__sbr_cell_3_820:
    mov eax, DWORD PTR [rbp-56]
__sbr_cell_3_820_end:
__sbr_cell_3_821:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_3_821_end:
__sbr_cell_3_822:
    mov edx, eax
__sbr_cell_3_822_end:
__sbr_cell_3_823:
    neg edx
__sbr_cell_3_823_end:
__sbr_cell_3_824:
    sub ecx, eax
__sbr_cell_3_824_end:
__sbr_cell_3_825:
    cmp r12d, ecx
__sbr_cell_3_825_end:
__sbr_cell_3_826:
    cmovl ecx, r12d
__sbr_cell_3_826_end:
__sbr_cell_3_827:
    cmp r12d, edx
__sbr_cell_3_827_end:
__sbr_cell_3_828:
    cmovl ecx, edx
__sbr_cell_3_828_end:
__sbr_cell_3_829:
    add ecx, eax
__sbr_cell_3_829_end:
__sbr_cell_3_830:
    mov DWORD PTR [rbp-56], ecx
__sbr_cell_3_830_end:
__sbr_cell_3_831:
    jmp ff_aac_sbr_decode_extension.L4e2
__sbr_cell_3_831_end:
ff_aac_sbr_decode_extension.Lcf6:
__sbr_cell_3_832:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_3_832_end:
__sbr_cell_3_833:
    int3
__sbr_cell_3_833_end:
__sbr_cell_3_834:
    int3
__sbr_cell_3_834_end:
__sbr_cell_3_835:
    int3
__sbr_cell_3_835_end:
__sbr_cell_3_836:
    int3
__sbr_cell_3_836_end:
__sbr_cell_3_837:
    int3
__sbr_cell_3_837_end:
.size ff_aac_sbr_decode_extension, .-ff_aac_sbr_decode_extension
.section .text.ff_aac_sbr_decode_usac_data,"ax",@progbits
.globl ff_aac_sbr_decode_usac_data
.type ff_aac_sbr_decode_usac_data,@function
ff_aac_sbr_decode_usac_data:
__sbr_cell_4_0:
    push rbp
__sbr_cell_4_0_end:
__sbr_cell_4_1:
    mov rbp, rsp
__sbr_cell_4_1_end:
__sbr_cell_4_2:
    push r15
__sbr_cell_4_2_end:
__sbr_cell_4_3:
    push r14
__sbr_cell_4_3_end:
__sbr_cell_4_4:
    push r13
__sbr_cell_4_4_end:
__sbr_cell_4_5:
    push r12
__sbr_cell_4_5_end:
__sbr_cell_4_6:
    push rbx
__sbr_cell_4_6_end:
__sbr_cell_4_7:
    sub rsp, 24
__sbr_cell_4_7_end:
ff_aac_sbr_decode_usac_data.L3361:
__sbr_cell_4_8:
    mov r15d, r8d
__sbr_cell_4_8_end:
__sbr_cell_4_9:
    mov r14, rcx
__sbr_cell_4_9_end:
__sbr_cell_4_10:
    mov rbx, rsi
__sbr_cell_4_10_end:
__sbr_cell_4_11:
    mov r12, rdi
__sbr_cell_4_11_end:
__sbr_cell_4_12:
    lea r13, [rsi+166176]
__sbr_cell_4_12_end:
__sbr_cell_4_13:
    mov DWORD PTR [rsi+166200], 0
__sbr_cell_4_13_end:
__sbr_cell_4_14:
    mov DWORD PTR [rsi+166192], 1
__sbr_cell_4_14_end:
ff_aac_sbr_decode_usac_data.L3388:
__sbr_cell_4_15:
    mov eax, DWORD PTR [rdi+22516]
__sbr_cell_4_15_end:
__sbr_cell_4_16:
    mov DWORD PTR [rsi+166176], eax
__sbr_cell_4_16_end:
__sbr_cell_4_17:
    xor eax, eax
__sbr_cell_4_17_end:
__sbr_cell_4_18:
    cmp r8d, 2
__sbr_cell_4_18_end:
__sbr_cell_4_19:
    sete al
__sbr_cell_4_19_end:
__sbr_cell_4_20:
    mov DWORD PTR [rsi+166188], eax
__sbr_cell_4_20_end:
ff_aac_sbr_decode_usac_data.L33a3:
__sbr_cell_4_21:
    mov ecx, DWORD PTR [rcx+8]
__sbr_cell_4_21_end:
__sbr_cell_4_22:
    mov rsi, QWORD PTR [r14+0]
__sbr_cell_4_22_end:
__sbr_cell_4_23:
    mov DWORD PTR [rbp-44], r9d
__sbr_cell_4_23_end:
__sbr_cell_4_24:
    test r9d, r9d
__sbr_cell_4_24_end:
__sbr_cell_4_25:
    je ff_aac_sbr_decode_usac_data.L33ba
__sbr_cell_4_25_end:
__sbr_cell_4_26:
    mov edi, DWORD PTR [r14+16]
__sbr_cell_4_26_end:
__sbr_cell_4_27:
    xor eax, eax
__sbr_cell_4_27_end:
__sbr_cell_4_28:
    jmp ff_aac_sbr_decode_usac_data.L3410
__sbr_cell_4_28_end:
ff_aac_sbr_decode_usac_data.L33ba:
__sbr_cell_4_29:
    mov r8d, ecx
__sbr_cell_4_29_end:
__sbr_cell_4_30:
    shr r8d, 3
__sbr_cell_4_30_end:
__sbr_cell_4_31:
    mov edi, DWORD PTR [r14+16]
__sbr_cell_4_31_end:
__sbr_cell_4_32:
    xor eax, eax
__sbr_cell_4_32_end:
__sbr_cell_4_33:
    cmp ecx, edi
__sbr_cell_4_33_end:
__sbr_cell_4_34:
    setl al
__sbr_cell_4_34_end:
__sbr_cell_4_35:
    add eax, ecx
__sbr_cell_4_35_end:
__sbr_cell_4_36:
    movzx r8d, BYTE PTR [rsi+r8*1+0]
__sbr_cell_4_36_end:
__sbr_cell_4_37:
    mov DWORD PTR [r14+8], eax
__sbr_cell_4_37_end:
__sbr_cell_4_38:
    and cl, 7
__sbr_cell_4_38_end:
__sbr_cell_4_39:
    shl r8d, cl
__sbr_cell_4_39_end:
__sbr_cell_4_40:
    test r8b, r8b
__sbr_cell_4_40_end:
__sbr_cell_4_41:
    jns ff_aac_sbr_decode_usac_data.L35bf
__sbr_cell_4_41_end:
ff_aac_sbr_decode_usac_data.L33e6:
__sbr_cell_4_42:
    mov ecx, eax
__sbr_cell_4_42_end:
__sbr_cell_4_43:
    shr ecx, 3
__sbr_cell_4_43_end:
__sbr_cell_4_44:
    xor r8d, r8d
__sbr_cell_4_44_end:
__sbr_cell_4_45:
    cmp eax, edi
__sbr_cell_4_45_end:
__sbr_cell_4_46:
    setl r8b
__sbr_cell_4_46_end:
__sbr_cell_4_47:
    add r8d, eax
__sbr_cell_4_47_end:
__sbr_cell_4_48:
    movzx r9d, BYTE PTR [rsi+rcx*1+0]
__sbr_cell_4_48_end:
__sbr_cell_4_49:
    and al, 7
__sbr_cell_4_49_end:
__sbr_cell_4_50:
    mov ecx, eax
__sbr_cell_4_50_end:
__sbr_cell_4_51:
    shl r9d, cl
__sbr_cell_4_51_end:
__sbr_cell_4_52:
    mov rcx, r8
__sbr_cell_4_52_end:
__sbr_cell_4_53:
    mov DWORD PTR [r14+8], ecx
__sbr_cell_4_53_end:
__sbr_cell_4_54:
    test r9b, r9b
__sbr_cell_4_54_end:
__sbr_cell_4_55:
    setns al
__sbr_cell_4_55_end:
ff_aac_sbr_decode_usac_data.L3410:
__sbr_cell_4_56:
    mov r8d, ecx
__sbr_cell_4_56_end:
__sbr_cell_4_57:
    shr r8d, 3
__sbr_cell_4_57_end:
__sbr_cell_4_58:
    xor r9d, r9d
__sbr_cell_4_58_end:
__sbr_cell_4_59:
    cmp ecx, edi
__sbr_cell_4_59_end:
__sbr_cell_4_60:
    setl r9b
__sbr_cell_4_60_end:
__sbr_cell_4_61:
    add r9d, ecx
__sbr_cell_4_61_end:
__sbr_cell_4_62:
    movzx esi, BYTE PTR [rsi+r8*1+0]
__sbr_cell_4_62_end:
__sbr_cell_4_63:
    and cl, 7
__sbr_cell_4_63_end:
__sbr_cell_4_64:
    shl esi, cl
__sbr_cell_4_64_end:
__sbr_cell_4_65:
    shr esi, 7
__sbr_cell_4_65_end:
__sbr_cell_4_66:
    mov DWORD PTR [r14+8], r9d
__sbr_cell_4_66_end:
__sbr_cell_4_67:
    and esi, 1
__sbr_cell_4_67_end:
__sbr_cell_4_68:
    mov DWORD PTR [rbx+166212], esi
__sbr_cell_4_68_end:
ff_aac_sbr_decode_usac_data.L343d:
__sbr_cell_4_69:
    mov esi, DWORD PTR [r14+8]
__sbr_cell_4_69_end:
__sbr_cell_4_70:
    mov edi, DWORD PTR [r14+16]
__sbr_cell_4_70_end:
__sbr_cell_4_71:
    mov rcx, QWORD PTR [r14+0]
__sbr_cell_4_71_end:
__sbr_cell_4_72:
    mov r8d, esi
__sbr_cell_4_72_end:
__sbr_cell_4_73:
    shr r8d, 3
__sbr_cell_4_73_end:
__sbr_cell_4_74:
    mov r8d, DWORD PTR [rcx+r8*1+0]
__sbr_cell_4_74_end:
__sbr_cell_4_75:
    bswap r8d
__sbr_cell_4_75_end:
__sbr_cell_4_76:
    mov ecx, esi
__sbr_cell_4_76_end:
__sbr_cell_4_77:
    and cl, 7
__sbr_cell_4_77_end:
__sbr_cell_4_78:
    shl r8d, cl
__sbr_cell_4_78_end:
__sbr_cell_4_79:
    shr r8d, 28
__sbr_cell_4_79_end:
__sbr_cell_4_80:
    add esi, 4
__sbr_cell_4_80_end:
__sbr_cell_4_81:
    cmp edi, esi
__sbr_cell_4_81_end:
__sbr_cell_4_82:
    cmovb esi, edi
__sbr_cell_4_82_end:
__sbr_cell_4_83:
    mov DWORD PTR [r14+8], esi
__sbr_cell_4_83_end:
__sbr_cell_4_84:
    mov BYTE PTR [rbx+166206], r8b
__sbr_cell_4_84_end:
ff_aac_sbr_decode_usac_data.L3475:
__sbr_cell_4_85:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_85_end:
__sbr_cell_4_86:
    mov rsi, QWORD PTR [r14+0]
__sbr_cell_4_86_end:
__sbr_cell_4_87:
    mov edi, ecx
__sbr_cell_4_87_end:
__sbr_cell_4_88:
    shr edi, 3
__sbr_cell_4_88_end:
__sbr_cell_4_89:
    xor r8d, r8d
__sbr_cell_4_89_end:
__sbr_cell_4_90:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_90_end:
__sbr_cell_4_91:
    setl r8b
__sbr_cell_4_91_end:
__sbr_cell_4_92:
    add r8d, ecx
__sbr_cell_4_92_end:
__sbr_cell_4_93:
    movzx esi, BYTE PTR [rsi+rdi*1+0]
__sbr_cell_4_93_end:
__sbr_cell_4_94:
    and cl, 7
__sbr_cell_4_94_end:
__sbr_cell_4_95:
    shl esi, cl
__sbr_cell_4_95_end:
__sbr_cell_4_96:
    shr esi, 7
__sbr_cell_4_96_end:
__sbr_cell_4_97:
    mov DWORD PTR [r14+8], r8d
__sbr_cell_4_97_end:
__sbr_cell_4_98:
    and esi, 1
__sbr_cell_4_98_end:
__sbr_cell_4_99:
    mov DWORD PTR [rbx+166216], esi
__sbr_cell_4_99_end:
__sbr_cell_4_100:
    test al, al
__sbr_cell_4_100_end:
__sbr_cell_4_101:
    jne ff_aac_sbr_decode_usac_data.L35bf
__sbr_cell_4_101_end:
ff_aac_sbr_decode_usac_data.L34b0:
__sbr_cell_4_102:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_102_end:
__sbr_cell_4_103:
    mov rax, QWORD PTR [r14+0]
__sbr_cell_4_103_end:
__sbr_cell_4_104:
    mov esi, ecx
__sbr_cell_4_104_end:
__sbr_cell_4_105:
    shr esi, 3
__sbr_cell_4_105_end:
__sbr_cell_4_106:
    xor edi, edi
__sbr_cell_4_106_end:
__sbr_cell_4_107:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_107_end:
__sbr_cell_4_108:
    setl dil
__sbr_cell_4_108_end:
__sbr_cell_4_109:
    add edi, ecx
__sbr_cell_4_109_end:
__sbr_cell_4_110:
    movzx eax, BYTE PTR [rax+rsi*1+0]
__sbr_cell_4_110_end:
__sbr_cell_4_111:
    mov DWORD PTR [r14+8], edi
__sbr_cell_4_111_end:
__sbr_cell_4_112:
    and cl, 7
__sbr_cell_4_112_end:
__sbr_cell_4_113:
    shl eax, cl
__sbr_cell_4_113_end:
__sbr_cell_4_114:
    test al, al
__sbr_cell_4_114_end:
__sbr_cell_4_115:
    jns ff_aac_sbr_decode_usac_data.L35a5
__sbr_cell_4_115_end:
ff_aac_sbr_decode_usac_data.L34dd:
__sbr_cell_4_116:
    mov eax, DWORD PTR [rbx+166220]
__sbr_cell_4_116_end:
__sbr_cell_4_117:
    movzx ecx, WORD PTR [rbx+166208]
__sbr_cell_4_117_end:
__sbr_cell_4_118:
    mov WORD PTR [rbp-48], cx
__sbr_cell_4_118_end:
__sbr_cell_4_119:
    mov ecx, DWORD PTR [rbx+166204]
__sbr_cell_4_119_end:
__sbr_cell_4_120:
    mov DWORD PTR [rbp-52], ecx
__sbr_cell_4_120_end:
ff_aac_sbr_decode_usac_data.L34f7:
__sbr_cell_4_121:
    mov ecx, DWORD PTR [rdx+12]
__sbr_cell_4_121_end:
__sbr_cell_4_122:
    shr ecx, 1
__sbr_cell_4_122_end:
__sbr_cell_4_123:
    and ecx, 1
__sbr_cell_4_123_end:
__sbr_cell_4_124:
    mov DWORD PTR [rbx+166196], ecx
__sbr_cell_4_124_end:
__sbr_cell_4_125:
    movzx ecx, BYTE PTR [rdx+13]
__sbr_cell_4_125_end:
__sbr_cell_4_126:
    mov BYTE PTR [rbx+166204], cl
__sbr_cell_4_126_end:
ff_aac_sbr_decode_usac_data.L350f:
__sbr_cell_4_127:
    movzx ecx, BYTE PTR [rdx+14]
__sbr_cell_4_127_end:
__sbr_cell_4_128:
    mov BYTE PTR [rbx+166205], cl
__sbr_cell_4_128_end:
__sbr_cell_4_129:
    movzx ecx, BYTE PTR [rdx+15]
__sbr_cell_4_129_end:
__sbr_cell_4_130:
    mov BYTE PTR [rbx+166207], cl
__sbr_cell_4_130_end:
ff_aac_sbr_decode_usac_data.L3523:
__sbr_cell_4_131:
    movzx ecx, BYTE PTR [rdx+16]
__sbr_cell_4_131_end:
__sbr_cell_4_132:
    and cl, 1
__sbr_cell_4_132_end:
__sbr_cell_4_133:
    mov BYTE PTR [rbx+166208], cl
__sbr_cell_4_133_end:
__sbr_cell_4_134:
    movzx ecx, BYTE PTR [rdx+17]
__sbr_cell_4_134_end:
__sbr_cell_4_135:
    mov BYTE PTR [rbx+166209], cl
__sbr_cell_4_135_end:
ff_aac_sbr_decode_usac_data.L353a:
__sbr_cell_4_136:
    movzx ecx, BYTE PTR [rdx+18]
__sbr_cell_4_136_end:
__sbr_cell_4_137:
    mov DWORD PTR [rbx+166220], ecx
__sbr_cell_4_137_end:
__sbr_cell_4_138:
    movzx esi, BYTE PTR [rdx+19]
__sbr_cell_4_138_end:
__sbr_cell_4_139:
    mov DWORD PTR [rbx+166224], esi
__sbr_cell_4_139_end:
ff_aac_sbr_decode_usac_data.L354e:
__sbr_cell_4_140:
    movzx esi, BYTE PTR [rdx+20]
__sbr_cell_4_140_end:
__sbr_cell_4_141:
    and esi, 1
__sbr_cell_4_141_end:
__sbr_cell_4_142:
    mov DWORD PTR [rbx+166228], esi
__sbr_cell_4_142_end:
__sbr_cell_4_143:
    mov edx, DWORD PTR [rdx+20]
__sbr_cell_4_143_end:
__sbr_cell_4_144:
    shr edx, 1
__sbr_cell_4_144_end:
__sbr_cell_4_145:
    and edx, 1
__sbr_cell_4_145_end:
__sbr_cell_4_146:
    mov DWORD PTR [rbx+166232], edx
__sbr_cell_4_146_end:
ff_aac_sbr_decode_usac_data.L3569:
__sbr_cell_4_147:
    mov edx, DWORD PTR [rbp-52]
__sbr_cell_4_147_end:
__sbr_cell_4_148:
    xor edx, DWORD PTR [rbx+166204]
__sbr_cell_4_148_end:
__sbr_cell_4_149:
    movzx esi, WORD PTR [rbp-48]
__sbr_cell_4_149_end:
__sbr_cell_4_150:
    xor si, WORD PTR [rbx+166208]
__sbr_cell_4_150_end:
__sbr_cell_4_151:
    movzx esi, si
__sbr_cell_4_151_end:
__sbr_cell_4_152:
    or esi, edx
__sbr_cell_4_152_end:
__sbr_cell_4_153:
    je ff_aac_sbr_decode_usac_data.L358e
__sbr_cell_4_153_end:
__sbr_cell_4_154:
    mov DWORD PTR [rbx+166200], 1
__sbr_cell_4_154_end:
ff_aac_sbr_decode_usac_data.L358e:
__sbr_cell_4_155:
    cmp eax, ecx
__sbr_cell_4_155_end:
__sbr_cell_4_156:
    je ff_aac_sbr_decode_usac_data.L35b5
__sbr_cell_4_156_end:
__sbr_cell_4_157:
    cmp DWORD PTR [rbx+166200], 0
__sbr_cell_4_157_end:
__sbr_cell_4_158:
    jne ff_aac_sbr_decode_usac_data.L35b5
__sbr_cell_4_158_end:
ff_aac_sbr_decode_usac_data.L359b:
__sbr_cell_4_159:
    mov rdi, r13
__sbr_cell_4_159_end:
__sbr_cell_4_160:
    call sbr_make_f_tablelim
__sbr_cell_4_160_end:
ff_aac_sbr_decode_usac_data.L35a3:
__sbr_cell_4_161:
    jmp ff_aac_sbr_decode_usac_data.L35b5
__sbr_cell_4_161_end:
ff_aac_sbr_decode_usac_data.L35a5:
__sbr_cell_4_162:
    mov rdi, r13
__sbr_cell_4_162_end:
__sbr_cell_4_163:
    mov rsi, r14
__sbr_cell_4_163_end:
__sbr_cell_4_164:
    mov edx, 1
__sbr_cell_4_164_end:
__sbr_cell_4_165:
    call read_sbr_header
__sbr_cell_4_165_end:
ff_aac_sbr_decode_usac_data.L35b5:
__sbr_cell_4_166:
    mov DWORD PTR [rbx+166180], 1
__sbr_cell_4_166_end:
ff_aac_sbr_decode_usac_data.L35bf:
__sbr_cell_4_167:
    mov eax, DWORD PTR [rbx+166264]
__sbr_cell_4_167_end:
__sbr_cell_4_168:
    mov ecx, DWORD PTR [rbx+166272]
__sbr_cell_4_168_end:
__sbr_cell_4_169:
    mov DWORD PTR [rbx+166260], eax
__sbr_cell_4_169_end:
__sbr_cell_4_170:
    mov DWORD PTR [rbx+166268], ecx
__sbr_cell_4_170_end:
ff_aac_sbr_decode_usac_data.L35d7:
__sbr_cell_4_171:
    mov DWORD PTR [rbx+166276], 1
__sbr_cell_4_171_end:
__sbr_cell_4_172:
    cmp DWORD PTR [rbx+166200], 0
__sbr_cell_4_172_end:
__sbr_cell_4_173:
    je ff_aac_sbr_decode_usac_data.L35f5
__sbr_cell_4_173_end:
ff_aac_sbr_decode_usac_data.L35ea:
__sbr_cell_4_174:
    mov rdi, r12
__sbr_cell_4_174_end:
__sbr_cell_4_175:
    mov rsi, r13
__sbr_cell_4_175_end:
__sbr_cell_4_176:
    call sbr_reset
__sbr_cell_4_176_end:
ff_aac_sbr_decode_usac_data.L35f5:
__sbr_cell_4_177:
    mov DWORD PTR [rbx+166184], 1
__sbr_cell_4_177_end:
__sbr_cell_4_178:
    cmp r15d, 1
__sbr_cell_4_178_end:
__sbr_cell_4_179:
    jne ff_aac_sbr_decode_usac_data.L36c7
__sbr_cell_4_179_end:
ff_aac_sbr_decode_usac_data.L3609:
__sbr_cell_4_180:
    lea r15, [rbx+166304]
__sbr_cell_4_180_end:
__sbr_cell_4_181:
    mov rdi, r12
__sbr_cell_4_181_end:
__sbr_cell_4_182:
    mov rsi, r13
__sbr_cell_4_182_end:
__sbr_cell_4_183:
    mov rdx, r14
__sbr_cell_4_183_end:
__sbr_cell_4_184:
    mov rcx, r15
__sbr_cell_4_184_end:
__sbr_cell_4_185:
    call read_sbr_grid
__sbr_cell_4_185_end:
ff_aac_sbr_decode_usac_data.L3621:
__sbr_cell_4_186:
    mov ecx, eax
__sbr_cell_4_186_end:
__sbr_cell_4_187:
    mov eax, 4294967295
__sbr_cell_4_187_end:
__sbr_cell_4_188:
    test ecx, ecx
__sbr_cell_4_188_end:
__sbr_cell_4_189:
    jne ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_189_end:
ff_aac_sbr_decode_usac_data.L3630:
__sbr_cell_4_190:
    mov edi, DWORD PTR [rbx+166192]
__sbr_cell_4_190_end:
__sbr_cell_4_191:
    mov rsi, r14
__sbr_cell_4_191_end:
__sbr_cell_4_192:
    mov rdx, r15
__sbr_cell_4_192_end:
__sbr_cell_4_193:
    mov ecx, DWORD PTR [rbp-44]
__sbr_cell_4_193_end:
__sbr_cell_4_194:
    call read_sbr_dtdf
__sbr_cell_4_194_end:
ff_aac_sbr_decode_usac_data.L3644:
__sbr_cell_4_195:
    mov rdi, r13
__sbr_cell_4_195_end:
__sbr_cell_4_196:
    mov rsi, r14
__sbr_cell_4_196_end:
__sbr_cell_4_197:
    mov rdx, r15
__sbr_cell_4_197_end:
__sbr_cell_4_198:
    call read_sbr_invf
__sbr_cell_4_198_end:
ff_aac_sbr_decode_usac_data.L3652:
__sbr_cell_4_199:
    mov rdi, r12
__sbr_cell_4_199_end:
__sbr_cell_4_200:
    mov rsi, r13
__sbr_cell_4_200_end:
__sbr_cell_4_201:
    mov rdx, r14
__sbr_cell_4_201_end:
__sbr_cell_4_202:
    mov rcx, r15
__sbr_cell_4_202_end:
__sbr_cell_4_203:
    xor r8d, r8d
__sbr_cell_4_203_end:
__sbr_cell_4_204:
    call read_sbr_envelope
__sbr_cell_4_204_end:
ff_aac_sbr_decode_usac_data.L3666:
__sbr_cell_4_205:
    test eax, eax
__sbr_cell_4_205_end:
__sbr_cell_4_206:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_206_end:
ff_aac_sbr_decode_usac_data.L366e:
__sbr_cell_4_207:
    mov rdi, r12
__sbr_cell_4_207_end:
__sbr_cell_4_208:
    mov rsi, r13
__sbr_cell_4_208_end:
__sbr_cell_4_209:
    mov rdx, r14
__sbr_cell_4_209_end:
__sbr_cell_4_210:
    mov rcx, r15
__sbr_cell_4_210_end:
__sbr_cell_4_211:
    xor r8d, r8d
__sbr_cell_4_211_end:
__sbr_cell_4_212:
    call read_sbr_noise
__sbr_cell_4_212_end:
ff_aac_sbr_decode_usac_data.L3682:
__sbr_cell_4_213:
    test eax, eax
__sbr_cell_4_213_end:
__sbr_cell_4_214:
    js ff_aac_sbr_decode_usac_data.L3aac
__sbr_cell_4_214_end:
ff_aac_sbr_decode_usac_data.L368a:
__sbr_cell_4_215:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_215_end:
__sbr_cell_4_216:
    mov eax, ecx
__sbr_cell_4_216_end:
__sbr_cell_4_217:
    shr eax, 3
__sbr_cell_4_217_end:
__sbr_cell_4_218:
    xor edx, edx
__sbr_cell_4_218_end:
__sbr_cell_4_219:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_219_end:
__sbr_cell_4_220:
    mov rsi, QWORD PTR [r14+0]
__sbr_cell_4_220_end:
__sbr_cell_4_221:
    setl dl
__sbr_cell_4_221_end:
__sbr_cell_4_222:
    add edx, ecx
__sbr_cell_4_222_end:
__sbr_cell_4_223:
    movzx eax, BYTE PTR [rsi+rax*1+0]
__sbr_cell_4_223_end:
__sbr_cell_4_224:
    and cl, 7
__sbr_cell_4_224_end:
__sbr_cell_4_225:
    shl eax, cl
__sbr_cell_4_225_end:
__sbr_cell_4_226:
    shr eax, 7
__sbr_cell_4_226_end:
__sbr_cell_4_227:
    mov DWORD PTR [r14+8], edx
__sbr_cell_4_227_end:
__sbr_cell_4_228:
    and eax, 1
__sbr_cell_4_228_end:
__sbr_cell_4_229:
    mov DWORD PTR [rbx+166308], eax
__sbr_cell_4_229_end:
__sbr_cell_4_230:
    jne ff_aac_sbr_decode_usac_data.L3ab1
__sbr_cell_4_230_end:
ff_aac_sbr_decode_usac_data.L36c0:
__sbr_cell_4_231:
    xor eax, eax
__sbr_cell_4_231_end:
__sbr_cell_4_232:
    jmp ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_232_end:
ff_aac_sbr_decode_usac_data.L36c7:
__sbr_cell_4_233:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_233_end:
__sbr_cell_4_234:
    mov eax, ecx
__sbr_cell_4_234_end:
__sbr_cell_4_235:
    shr eax, 3
__sbr_cell_4_235_end:
__sbr_cell_4_236:
    xor edx, edx
__sbr_cell_4_236_end:
__sbr_cell_4_237:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_237_end:
__sbr_cell_4_238:
    mov rsi, QWORD PTR [r14+0]
__sbr_cell_4_238_end:
__sbr_cell_4_239:
    setl dl
__sbr_cell_4_239_end:
__sbr_cell_4_240:
    add edx, ecx
__sbr_cell_4_240_end:
__sbr_cell_4_241:
    movzx eax, BYTE PTR [rsi+rax*1+0]
__sbr_cell_4_241_end:
__sbr_cell_4_242:
    and cl, 7
__sbr_cell_4_242_end:
__sbr_cell_4_243:
    shl eax, cl
__sbr_cell_4_243_end:
__sbr_cell_4_244:
    mov DWORD PTR [r14+8], edx
__sbr_cell_4_244_end:
__sbr_cell_4_245:
    lea r15, [rbx+166304]
__sbr_cell_4_245_end:
__sbr_cell_4_246:
    test al, al
__sbr_cell_4_246_end:
__sbr_cell_4_247:
    jns ff_aac_sbr_decode_usac_data.L3933
__sbr_cell_4_247_end:
ff_aac_sbr_decode_usac_data.L36fa:
__sbr_cell_4_248:
    mov DWORD PTR [rbx+166236], 1
__sbr_cell_4_248_end:
__sbr_cell_4_249:
    mov rdi, r12
__sbr_cell_4_249_end:
__sbr_cell_4_250:
    mov rsi, r13
__sbr_cell_4_250_end:
__sbr_cell_4_251:
    mov rdx, r14
__sbr_cell_4_251_end:
__sbr_cell_4_252:
    mov rcx, r15
__sbr_cell_4_252_end:
__sbr_cell_4_253:
    call read_sbr_grid
__sbr_cell_4_253_end:
ff_aac_sbr_decode_usac_data.L3715:
__sbr_cell_4_254:
    mov ecx, eax
__sbr_cell_4_254_end:
__sbr_cell_4_255:
    mov eax, 4294967295
__sbr_cell_4_255_end:
__sbr_cell_4_256:
    test ecx, ecx
__sbr_cell_4_256_end:
__sbr_cell_4_257:
    jne ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_257_end:
ff_aac_sbr_decode_usac_data.L3724:
__sbr_cell_4_258:
    mov eax, DWORD PTR [rbx+255080]
__sbr_cell_4_258_end:
__sbr_cell_4_259:
    cmp rax, 9
__sbr_cell_4_259_end:
__sbr_cell_4_260:
    jae ff_aac_sbr_decode_usac_data.L3f00
__sbr_cell_4_260_end:
ff_aac_sbr_decode_usac_data.L3734:
__sbr_cell_4_261:
    movzx ecx, BYTE PTR [rbx+rax*1+255084]
__sbr_cell_4_261_end:
__sbr_cell_4_262:
    mov BYTE PTR [rbx+255084], cl
__sbr_cell_4_262_end:
__sbr_cell_4_263:
    movzx ecx, BYTE PTR [rbx+rax*1+343804]
__sbr_cell_4_263_end:
__sbr_cell_4_264:
    mov BYTE PTR [rbx+343813], cl
__sbr_cell_4_264_end:
ff_aac_sbr_decode_usac_data.L3750:
__sbr_cell_4_265:
    xor ecx, ecx
__sbr_cell_4_265_end:
__sbr_cell_4_266:
    cmp DWORD PTR [rbx+269672], eax
__sbr_cell_4_266_end:
__sbr_cell_4_267:
    setne cl
__sbr_cell_4_267_end:
__sbr_cell_4_268:
    neg ecx
__sbr_cell_4_268_end:
__sbr_cell_4_269:
    mov DWORD PTR [rbx+269668], ecx
__sbr_cell_4_269_end:
ff_aac_sbr_decode_usac_data.L3763:
__sbr_cell_4_270:
    mov rax, QWORD PTR [rbx+166317]
__sbr_cell_4_270_end:
__sbr_cell_4_271:
    mov QWORD PTR [rbx+255085], rax
__sbr_cell_4_271_end:
__sbr_cell_4_272:
    mov rax, QWORD PTR [rbx+255036]
__sbr_cell_4_272_end:
__sbr_cell_4_273:
    mov QWORD PTR [rbx+343804], rax
__sbr_cell_4_273_end:
ff_aac_sbr_decode_usac_data.L377f:
__sbr_cell_4_274:
    movzx eax, BYTE PTR [rbx+255044]
__sbr_cell_4_274_end:
__sbr_cell_4_275:
    mov BYTE PTR [rbx+343812], al
__sbr_cell_4_275_end:
__sbr_cell_4_276:
    movzx eax, WORD PTR [rbx+255046]
__sbr_cell_4_276_end:
__sbr_cell_4_277:
    mov WORD PTR [rbx+343814], ax
__sbr_cell_4_277_end:
ff_aac_sbr_decode_usac_data.L379a:
__sbr_cell_4_278:
    movzx eax, BYTE PTR [rbx+255048]
__sbr_cell_4_278_end:
__sbr_cell_4_279:
    mov BYTE PTR [rbx+343816], al
__sbr_cell_4_279_end:
__sbr_cell_4_280:
    mov eax, DWORD PTR [rbx+166312]
__sbr_cell_4_280_end:
__sbr_cell_4_281:
    mov DWORD PTR [rbx+255080], eax
__sbr_cell_4_281_end:
ff_aac_sbr_decode_usac_data.L37b3:
__sbr_cell_4_282:
    mov eax, DWORD PTR [rbx+166404]
__sbr_cell_4_282_end:
__sbr_cell_4_283:
    mov DWORD PTR [rbx+255172], eax
__sbr_cell_4_283_end:
__sbr_cell_4_284:
    mov eax, DWORD PTR [rbx+166328]
__sbr_cell_4_284_end:
__sbr_cell_4_285:
    mov DWORD PTR [rbx+255096], eax
__sbr_cell_4_285_end:
ff_aac_sbr_decode_usac_data.L37cb:
__sbr_cell_4_286:
    mov eax, DWORD PTR [rbx+166304]
__sbr_cell_4_286_end:
__sbr_cell_4_287:
    mov DWORD PTR [rbx+255072], eax
__sbr_cell_4_287_end:
__sbr_cell_4_288:
    mov eax, DWORD PTR [rbx+180904]
__sbr_cell_4_288_end:
__sbr_cell_4_289:
    mov DWORD PTR [rbx+269672], eax
__sbr_cell_4_289_end:
ff_aac_sbr_decode_usac_data.L37e3:
__sbr_cell_4_290:
    mov edi, DWORD PTR [rbx+166192]
__sbr_cell_4_290_end:
__sbr_cell_4_291:
    mov rsi, r14
__sbr_cell_4_291_end:
__sbr_cell_4_292:
    mov rdx, r15
__sbr_cell_4_292_end:
__sbr_cell_4_293:
    mov r13, r15
__sbr_cell_4_293_end:
__sbr_cell_4_294:
    mov r15d, DWORD PTR [rbp-44]
__sbr_cell_4_294_end:
__sbr_cell_4_295:
    mov ecx, r15d
__sbr_cell_4_295_end:
__sbr_cell_4_296:
    call read_sbr_dtdf
__sbr_cell_4_296_end:
ff_aac_sbr_decode_usac_data.L37fe:
__sbr_cell_4_297:
    mov edi, DWORD PTR [rbx+166192]
__sbr_cell_4_297_end:
__sbr_cell_4_298:
    mov rsi, r14
__sbr_cell_4_298_end:
__sbr_cell_4_299:
    lea rdx, [rbx+255072]
__sbr_cell_4_299_end:
__sbr_cell_4_300:
    mov ecx, r15d
__sbr_cell_4_300_end:
__sbr_cell_4_301:
    mov r15, r13
__sbr_cell_4_301_end:
__sbr_cell_4_302:
    call read_sbr_dtdf
__sbr_cell_4_302_end:
ff_aac_sbr_decode_usac_data.L3819:
__sbr_cell_4_303:
    lea r13, [rbx+166176]
__sbr_cell_4_303_end:
__sbr_cell_4_304:
    mov rdi, r13
__sbr_cell_4_304_end:
__sbr_cell_4_305:
    mov rsi, r14
__sbr_cell_4_305_end:
__sbr_cell_4_306:
    mov rdx, r15
__sbr_cell_4_306_end:
__sbr_cell_4_307:
    call read_sbr_invf
__sbr_cell_4_307_end:
ff_aac_sbr_decode_usac_data.L382e:
__sbr_cell_4_308:
    movzx eax, BYTE PTR [rbx+255115]
__sbr_cell_4_308_end:
__sbr_cell_4_309:
    mov BYTE PTR [rbx+255120], al
__sbr_cell_4_309_end:
__sbr_cell_4_310:
    mov eax, DWORD PTR [rbx+255111]
__sbr_cell_4_310_end:
__sbr_cell_4_311:
    mov DWORD PTR [rbx+255116], eax
__sbr_cell_4_311_end:
ff_aac_sbr_decode_usac_data.L3847:
__sbr_cell_4_312:
    mov eax, DWORD PTR [rbx+166343]
__sbr_cell_4_312_end:
__sbr_cell_4_313:
    mov DWORD PTR [rbx+255111], eax
__sbr_cell_4_313_end:
__sbr_cell_4_314:
    movzx eax, BYTE PTR [rbx+166347]
__sbr_cell_4_314_end:
__sbr_cell_4_315:
    mov BYTE PTR [rbx+255115], al
__sbr_cell_4_315_end:
ff_aac_sbr_decode_usac_data.L3860:
__sbr_cell_4_316:
    mov rdi, r12
__sbr_cell_4_316_end:
__sbr_cell_4_317:
    mov rsi, r13
__sbr_cell_4_317_end:
__sbr_cell_4_318:
    mov rdx, r14
__sbr_cell_4_318_end:
__sbr_cell_4_319:
    mov rcx, r15
__sbr_cell_4_319_end:
__sbr_cell_4_320:
    xor r8d, r8d
__sbr_cell_4_320_end:
__sbr_cell_4_321:
    call read_sbr_envelope
__sbr_cell_4_321_end:
ff_aac_sbr_decode_usac_data.L3874:
__sbr_cell_4_322:
    test eax, eax
__sbr_cell_4_322_end:
__sbr_cell_4_323:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_323_end:
ff_aac_sbr_decode_usac_data.L387c:
__sbr_cell_4_324:
    mov rdi, r12
__sbr_cell_4_324_end:
__sbr_cell_4_325:
    mov rsi, r13
__sbr_cell_4_325_end:
__sbr_cell_4_326:
    mov rdx, r14
__sbr_cell_4_326_end:
__sbr_cell_4_327:
    mov rcx, r15
__sbr_cell_4_327_end:
__sbr_cell_4_328:
    xor r8d, r8d
__sbr_cell_4_328_end:
__sbr_cell_4_329:
    call read_sbr_noise
__sbr_cell_4_329_end:
ff_aac_sbr_decode_usac_data.L3890:
__sbr_cell_4_330:
    test eax, eax
__sbr_cell_4_330_end:
__sbr_cell_4_331:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_331_end:
ff_aac_sbr_decode_usac_data.L3898:
__sbr_cell_4_332:
    mov rdi, r12
__sbr_cell_4_332_end:
__sbr_cell_4_333:
    mov rsi, r13
__sbr_cell_4_333_end:
__sbr_cell_4_334:
    mov rdx, r14
__sbr_cell_4_334_end:
__sbr_cell_4_335:
    lea r15, [rbx+255072]
__sbr_cell_4_335_end:
__sbr_cell_4_336:
    mov rcx, r15
__sbr_cell_4_336_end:
__sbr_cell_4_337:
    mov r8d, 1
__sbr_cell_4_337_end:
__sbr_cell_4_338:
    call read_sbr_envelope
__sbr_cell_4_338_end:
ff_aac_sbr_decode_usac_data.L38b6:
__sbr_cell_4_339:
    test eax, eax
__sbr_cell_4_339_end:
__sbr_cell_4_340:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_340_end:
ff_aac_sbr_decode_usac_data.L38be:
__sbr_cell_4_341:
    mov rdi, r12
__sbr_cell_4_341_end:
__sbr_cell_4_342:
    mov rsi, r13
__sbr_cell_4_342_end:
__sbr_cell_4_343:
    mov rdx, r14
__sbr_cell_4_343_end:
__sbr_cell_4_344:
    mov rcx, r15
__sbr_cell_4_344_end:
__sbr_cell_4_345:
    mov r8d, 1
__sbr_cell_4_345_end:
__sbr_cell_4_346:
    call read_sbr_noise
__sbr_cell_4_346_end:
ff_aac_sbr_decode_usac_data.L38d5:
__sbr_cell_4_347:
    test eax, eax
__sbr_cell_4_347_end:
__sbr_cell_4_348:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_348_end:
ff_aac_sbr_decode_usac_data.L38dd:
__sbr_cell_4_349:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_349_end:
__sbr_cell_4_350:
    mov eax, ecx
__sbr_cell_4_350_end:
__sbr_cell_4_351:
    shr eax, 3
__sbr_cell_4_351_end:
__sbr_cell_4_352:
    xor edx, edx
__sbr_cell_4_352_end:
__sbr_cell_4_353:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_353_end:
__sbr_cell_4_354:
    mov rsi, QWORD PTR [r14+0]
__sbr_cell_4_354_end:
__sbr_cell_4_355:
    setl dl
__sbr_cell_4_355_end:
__sbr_cell_4_356:
    add edx, ecx
__sbr_cell_4_356_end:
__sbr_cell_4_357:
    movzx eax, BYTE PTR [rsi+rax*1+0]
__sbr_cell_4_357_end:
__sbr_cell_4_358:
    and cl, 7
__sbr_cell_4_358_end:
__sbr_cell_4_359:
    shl eax, cl
__sbr_cell_4_359_end:
__sbr_cell_4_360:
    shr eax, 7
__sbr_cell_4_360_end:
__sbr_cell_4_361:
    mov DWORD PTR [r14+8], edx
__sbr_cell_4_361_end:
__sbr_cell_4_362:
    and eax, 1
__sbr_cell_4_362_end:
__sbr_cell_4_363:
    mov DWORD PTR [rbx+166308], eax
__sbr_cell_4_363_end:
__sbr_cell_4_364:
    je ff_aac_sbr_decode_usac_data.L3c4b
__sbr_cell_4_364_end:
ff_aac_sbr_decode_usac_data.L3913:
__sbr_cell_4_365:
    movsxd rdx, DWORD PTR [rbx+477956]
__sbr_cell_4_365_end:
__sbr_cell_4_366:
    test rdx, rdx
__sbr_cell_4_366_end:
__sbr_cell_4_367:
    jle ff_aac_sbr_decode_usac_data.L3c4b
__sbr_cell_4_367_end:
__sbr_cell_4_368:
    cmp edx, 1
__sbr_cell_4_368_end:
__sbr_cell_4_369:
    jne ff_aac_sbr_decode_usac_data.L3b98
__sbr_cell_4_369_end:
__sbr_cell_4_370:
    xor eax, eax
__sbr_cell_4_370_end:
__sbr_cell_4_371:
    jmp ff_aac_sbr_decode_usac_data.L3c1c
__sbr_cell_4_371_end:
ff_aac_sbr_decode_usac_data.L3933:
__sbr_cell_4_372:
    mov DWORD PTR [rbx+166236], 0
__sbr_cell_4_372_end:
__sbr_cell_4_373:
    mov rdi, r12
__sbr_cell_4_373_end:
__sbr_cell_4_374:
    mov rsi, r13
__sbr_cell_4_374_end:
__sbr_cell_4_375:
    mov rdx, r14
__sbr_cell_4_375_end:
__sbr_cell_4_376:
    mov rcx, r15
__sbr_cell_4_376_end:
__sbr_cell_4_377:
    call read_sbr_grid
__sbr_cell_4_377_end:
ff_aac_sbr_decode_usac_data.L394e:
__sbr_cell_4_378:
    mov ecx, eax
__sbr_cell_4_378_end:
__sbr_cell_4_379:
    mov eax, 4294967295
__sbr_cell_4_379_end:
__sbr_cell_4_380:
    test ecx, ecx
__sbr_cell_4_380_end:
__sbr_cell_4_381:
    jne ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_381_end:
ff_aac_sbr_decode_usac_data.L395d:
__sbr_cell_4_382:
    lea rcx, [rbx+255072]
__sbr_cell_4_382_end:
__sbr_cell_4_383:
    mov rdi, r12
__sbr_cell_4_383_end:
__sbr_cell_4_384:
    mov rsi, r13
__sbr_cell_4_384_end:
__sbr_cell_4_385:
    mov rdx, r14
__sbr_cell_4_385_end:
__sbr_cell_4_386:
    call read_sbr_grid
__sbr_cell_4_386_end:
ff_aac_sbr_decode_usac_data.L3972:
__sbr_cell_4_387:
    mov ecx, eax
__sbr_cell_4_387_end:
__sbr_cell_4_388:
    mov eax, 4294967295
__sbr_cell_4_388_end:
__sbr_cell_4_389:
    test ecx, ecx
__sbr_cell_4_389_end:
__sbr_cell_4_390:
    jne ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_390_end:
ff_aac_sbr_decode_usac_data.L3981:
__sbr_cell_4_391:
    mov edi, DWORD PTR [rbx+166192]
__sbr_cell_4_391_end:
__sbr_cell_4_392:
    mov rsi, r14
__sbr_cell_4_392_end:
__sbr_cell_4_393:
    mov rdx, r15
__sbr_cell_4_393_end:
__sbr_cell_4_394:
    mov r15d, DWORD PTR [rbp-44]
__sbr_cell_4_394_end:
__sbr_cell_4_395:
    mov ecx, r15d
__sbr_cell_4_395_end:
__sbr_cell_4_396:
    call read_sbr_dtdf
__sbr_cell_4_396_end:
ff_aac_sbr_decode_usac_data.L3999:
__sbr_cell_4_397:
    mov edi, DWORD PTR [rbx+166192]
__sbr_cell_4_397_end:
__sbr_cell_4_398:
    mov rsi, r14
__sbr_cell_4_398_end:
__sbr_cell_4_399:
    lea rdx, [rbx+255072]
__sbr_cell_4_399_end:
__sbr_cell_4_400:
    mov ecx, r15d
__sbr_cell_4_400_end:
__sbr_cell_4_401:
    lea r15, [rbx+166304]
__sbr_cell_4_401_end:
__sbr_cell_4_402:
    call read_sbr_dtdf
__sbr_cell_4_402_end:
ff_aac_sbr_decode_usac_data.L39b8:
__sbr_cell_4_403:
    mov rdi, r13
__sbr_cell_4_403_end:
__sbr_cell_4_404:
    mov rsi, r14
__sbr_cell_4_404_end:
__sbr_cell_4_405:
    mov rdx, r15
__sbr_cell_4_405_end:
__sbr_cell_4_406:
    call read_sbr_invf
__sbr_cell_4_406_end:
ff_aac_sbr_decode_usac_data.L39c6:
__sbr_cell_4_407:
    mov rdi, r13
__sbr_cell_4_407_end:
__sbr_cell_4_408:
    mov rsi, r14
__sbr_cell_4_408_end:
__sbr_cell_4_409:
    lea rdx, [rbx+255072]
__sbr_cell_4_409_end:
__sbr_cell_4_410:
    call read_sbr_invf
__sbr_cell_4_410_end:
ff_aac_sbr_decode_usac_data.L39d8:
__sbr_cell_4_411:
    mov rdi, r12
__sbr_cell_4_411_end:
__sbr_cell_4_412:
    mov rsi, r13
__sbr_cell_4_412_end:
__sbr_cell_4_413:
    mov rdx, r14
__sbr_cell_4_413_end:
__sbr_cell_4_414:
    mov rcx, r15
__sbr_cell_4_414_end:
__sbr_cell_4_415:
    xor r8d, r8d
__sbr_cell_4_415_end:
__sbr_cell_4_416:
    call read_sbr_envelope
__sbr_cell_4_416_end:
ff_aac_sbr_decode_usac_data.L39ec:
__sbr_cell_4_417:
    test eax, eax
__sbr_cell_4_417_end:
__sbr_cell_4_418:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_418_end:
ff_aac_sbr_decode_usac_data.L39f4:
__sbr_cell_4_419:
    mov rdi, r12
__sbr_cell_4_419_end:
__sbr_cell_4_420:
    mov rsi, r13
__sbr_cell_4_420_end:
__sbr_cell_4_421:
    mov rdx, r14
__sbr_cell_4_421_end:
__sbr_cell_4_422:
    lea rcx, [rbx+255072]
__sbr_cell_4_422_end:
__sbr_cell_4_423:
    mov r8d, 1
__sbr_cell_4_423_end:
__sbr_cell_4_424:
    call read_sbr_envelope
__sbr_cell_4_424_end:
ff_aac_sbr_decode_usac_data.L3a0f:
__sbr_cell_4_425:
    test eax, eax
__sbr_cell_4_425_end:
__sbr_cell_4_426:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_426_end:
ff_aac_sbr_decode_usac_data.L3a17:
__sbr_cell_4_427:
    mov rdi, r12
__sbr_cell_4_427_end:
__sbr_cell_4_428:
    mov rsi, r13
__sbr_cell_4_428_end:
__sbr_cell_4_429:
    mov rdx, r14
__sbr_cell_4_429_end:
__sbr_cell_4_430:
    mov rcx, r15
__sbr_cell_4_430_end:
__sbr_cell_4_431:
    xor r8d, r8d
__sbr_cell_4_431_end:
__sbr_cell_4_432:
    call read_sbr_noise
__sbr_cell_4_432_end:
ff_aac_sbr_decode_usac_data.L3a2b:
__sbr_cell_4_433:
    test eax, eax
__sbr_cell_4_433_end:
__sbr_cell_4_434:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_434_end:
ff_aac_sbr_decode_usac_data.L3a33:
__sbr_cell_4_435:
    mov rdi, r12
__sbr_cell_4_435_end:
__sbr_cell_4_436:
    mov rsi, r13
__sbr_cell_4_436_end:
__sbr_cell_4_437:
    mov rdx, r14
__sbr_cell_4_437_end:
__sbr_cell_4_438:
    lea rcx, [rbx+255072]
__sbr_cell_4_438_end:
__sbr_cell_4_439:
    mov r8d, 1
__sbr_cell_4_439_end:
__sbr_cell_4_440:
    call read_sbr_noise
__sbr_cell_4_440_end:
ff_aac_sbr_decode_usac_data.L3a4e:
__sbr_cell_4_441:
    test eax, eax
__sbr_cell_4_441_end:
__sbr_cell_4_442:
    js ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_442_end:
ff_aac_sbr_decode_usac_data.L3a56:
__sbr_cell_4_443:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_443_end:
__sbr_cell_4_444:
    mov eax, ecx
__sbr_cell_4_444_end:
__sbr_cell_4_445:
    shr eax, 3
__sbr_cell_4_445_end:
__sbr_cell_4_446:
    xor edx, edx
__sbr_cell_4_446_end:
__sbr_cell_4_447:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_447_end:
__sbr_cell_4_448:
    mov rsi, QWORD PTR [r14+0]
__sbr_cell_4_448_end:
__sbr_cell_4_449:
    setl dl
__sbr_cell_4_449_end:
__sbr_cell_4_450:
    add edx, ecx
__sbr_cell_4_450_end:
__sbr_cell_4_451:
    movzx eax, BYTE PTR [rsi+rax*1+0]
__sbr_cell_4_451_end:
__sbr_cell_4_452:
    and cl, 7
__sbr_cell_4_452_end:
__sbr_cell_4_453:
    shl eax, cl
__sbr_cell_4_453_end:
__sbr_cell_4_454:
    shr eax, 7
__sbr_cell_4_454_end:
__sbr_cell_4_455:
    mov DWORD PTR [r14+8], edx
__sbr_cell_4_455_end:
__sbr_cell_4_456:
    and eax, 1
__sbr_cell_4_456_end:
__sbr_cell_4_457:
    mov DWORD PTR [rbx+166308], eax
__sbr_cell_4_457_end:
__sbr_cell_4_458:
    je ff_aac_sbr_decode_usac_data.L3e17
__sbr_cell_4_458_end:
ff_aac_sbr_decode_usac_data.L3a8c:
__sbr_cell_4_459:
    movsxd rdx, DWORD PTR [rbx+477956]
__sbr_cell_4_459_end:
__sbr_cell_4_460:
    test rdx, rdx
__sbr_cell_4_460_end:
__sbr_cell_4_461:
    jle ff_aac_sbr_decode_usac_data.L3e17
__sbr_cell_4_461_end:
__sbr_cell_4_462:
    cmp edx, 1
__sbr_cell_4_462_end:
__sbr_cell_4_463:
    jne ff_aac_sbr_decode_usac_data.L3d64
__sbr_cell_4_463_end:
__sbr_cell_4_464:
    xor eax, eax
__sbr_cell_4_464_end:
__sbr_cell_4_465:
    jmp ff_aac_sbr_decode_usac_data.L3de8
__sbr_cell_4_465_end:
ff_aac_sbr_decode_usac_data.L3aac:
__sbr_cell_4_466:
    jmp ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_466_end:
ff_aac_sbr_decode_usac_data.L3ab1:
__sbr_cell_4_467:
    movsxd rsi, DWORD PTR [rbx+477956]
__sbr_cell_4_467_end:
__sbr_cell_4_468:
    test rsi, rsi
__sbr_cell_4_468_end:
__sbr_cell_4_469:
    mov eax, 0
__sbr_cell_4_469_end:
__sbr_cell_4_470:
    jle ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_470_end:
__sbr_cell_4_471:
    xor eax, eax
__sbr_cell_4_471_end:
__sbr_cell_4_472:
    cmp esi, 1
__sbr_cell_4_472_end:
__sbr_cell_4_473:
    jne ff_aac_sbr_decode_usac_data.L3ad4
__sbr_cell_4_473_end:
__sbr_cell_4_474:
    xor edx, edx
__sbr_cell_4_474_end:
__sbr_cell_4_475:
    jmp ff_aac_sbr_decode_usac_data.L3b61
__sbr_cell_4_475_end:
ff_aac_sbr_decode_usac_data.L3ad4:
__sbr_cell_4_476:
    mov edi, esi
__sbr_cell_4_476_end:
__sbr_cell_4_477:
    and edi, 2147483646
__sbr_cell_4_477_end:
__sbr_cell_4_478:
    xor edx, edx
__sbr_cell_4_478_end:
__sbr_cell_4_479:
    .nops 1
__sbr_cell_4_479_end:
ff_aac_sbr_decode_usac_data.L3ae0:
__sbr_cell_4_480:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_480_end:
__sbr_cell_4_481:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_481_end:
__sbr_cell_4_482:
    mov r9d, ecx
__sbr_cell_4_482_end:
__sbr_cell_4_483:
    shr r9d, 3
__sbr_cell_4_483_end:
__sbr_cell_4_484:
    xor r10d, r10d
__sbr_cell_4_484_end:
__sbr_cell_4_485:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_485_end:
__sbr_cell_4_486:
    setl r10b
__sbr_cell_4_486_end:
__sbr_cell_4_487:
    add r10d, ecx
__sbr_cell_4_487_end:
__sbr_cell_4_488:
    movzx r8d, BYTE PTR [r8+r9*1+0]
__sbr_cell_4_488_end:
__sbr_cell_4_489:
    and cl, 7
__sbr_cell_4_489_end:
__sbr_cell_4_490:
    shl r8d, cl
__sbr_cell_4_490_end:
__sbr_cell_4_491:
    mov DWORD PTR [r14+8], r10d
__sbr_cell_4_491_end:
__sbr_cell_4_492:
    shr r8b, 7
__sbr_cell_4_492_end:
__sbr_cell_4_493:
    mov BYTE PTR [rbx+rdx*1+166353], r8b
__sbr_cell_4_493_end:
ff_aac_sbr_decode_usac_data.L3b17:
__sbr_cell_4_494:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_494_end:
__sbr_cell_4_495:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_495_end:
__sbr_cell_4_496:
    mov r9d, ecx
__sbr_cell_4_496_end:
__sbr_cell_4_497:
    shr r9d, 3
__sbr_cell_4_497_end:
__sbr_cell_4_498:
    xor r10d, r10d
__sbr_cell_4_498_end:
__sbr_cell_4_499:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_499_end:
__sbr_cell_4_500:
    setl r10b
__sbr_cell_4_500_end:
__sbr_cell_4_501:
    add r10d, ecx
__sbr_cell_4_501_end:
__sbr_cell_4_502:
    movzx r8d, BYTE PTR [r8+r9*1+0]
__sbr_cell_4_502_end:
__sbr_cell_4_503:
    and cl, 7
__sbr_cell_4_503_end:
__sbr_cell_4_504:
    shl r8d, cl
__sbr_cell_4_504_end:
__sbr_cell_4_505:
    mov DWORD PTR [r14+8], r10d
__sbr_cell_4_505_end:
__sbr_cell_4_506:
    shr r8b, 7
__sbr_cell_4_506_end:
__sbr_cell_4_507:
    mov BYTE PTR [rbx+rdx*1+166354], r8b
__sbr_cell_4_507_end:
__sbr_cell_4_508:
    add rdx, 2
__sbr_cell_4_508_end:
__sbr_cell_4_509:
    cmp rdi, rdx
__sbr_cell_4_509_end:
__sbr_cell_4_510:
    jne ff_aac_sbr_decode_usac_data.L3ae0
__sbr_cell_4_510_end:
__sbr_cell_4_511:
    test sil, 1
__sbr_cell_4_511_end:
__sbr_cell_4_512:
    je ff_aac_sbr_decode_usac_data.L36c0
__sbr_cell_4_512_end:
ff_aac_sbr_decode_usac_data.L3b61:
__sbr_cell_4_513:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_513_end:
__sbr_cell_4_514:
    mov esi, ecx
__sbr_cell_4_514_end:
__sbr_cell_4_515:
    shr esi, 3
__sbr_cell_4_515_end:
__sbr_cell_4_516:
    xor edi, edi
__sbr_cell_4_516_end:
__sbr_cell_4_517:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_517_end:
__sbr_cell_4_518:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_518_end:
__sbr_cell_4_519:
    setl dil
__sbr_cell_4_519_end:
__sbr_cell_4_520:
    add edi, ecx
__sbr_cell_4_520_end:
__sbr_cell_4_521:
    movzx esi, BYTE PTR [r8+rsi*1+0]
__sbr_cell_4_521_end:
__sbr_cell_4_522:
    and cl, 7
__sbr_cell_4_522_end:
__sbr_cell_4_523:
    shl esi, cl
__sbr_cell_4_523_end:
__sbr_cell_4_524:
    mov DWORD PTR [r14+8], edi
__sbr_cell_4_524_end:
__sbr_cell_4_525:
    shr sil, 7
__sbr_cell_4_525_end:
__sbr_cell_4_526:
    mov BYTE PTR [rbx+rdx*1+166353], sil
__sbr_cell_4_526_end:
__sbr_cell_4_527:
    jmp ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_527_end:
ff_aac_sbr_decode_usac_data.L3b98:
__sbr_cell_4_528:
    mov esi, edx
__sbr_cell_4_528_end:
__sbr_cell_4_529:
    and esi, 2147483646
__sbr_cell_4_529_end:
__sbr_cell_4_530:
    xor eax, eax
__sbr_cell_4_530_end:
ff_aac_sbr_decode_usac_data.L3ba2:
__sbr_cell_4_531:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_531_end:
__sbr_cell_4_532:
    mov rdi, QWORD PTR [r14+0]
__sbr_cell_4_532_end:
__sbr_cell_4_533:
    mov r8d, ecx
__sbr_cell_4_533_end:
__sbr_cell_4_534:
    shr r8d, 3
__sbr_cell_4_534_end:
__sbr_cell_4_535:
    xor r9d, r9d
__sbr_cell_4_535_end:
__sbr_cell_4_536:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_536_end:
__sbr_cell_4_537:
    setl r9b
__sbr_cell_4_537_end:
__sbr_cell_4_538:
    add r9d, ecx
__sbr_cell_4_538_end:
__sbr_cell_4_539:
    movzx edi, BYTE PTR [rdi+r8*1+0]
__sbr_cell_4_539_end:
__sbr_cell_4_540:
    and cl, 7
__sbr_cell_4_540_end:
__sbr_cell_4_541:
    shl edi, cl
__sbr_cell_4_541_end:
__sbr_cell_4_542:
    mov DWORD PTR [r14+8], r9d
__sbr_cell_4_542_end:
__sbr_cell_4_543:
    shr dil, 7
__sbr_cell_4_543_end:
__sbr_cell_4_544:
    mov BYTE PTR [rbx+rax*1+166353], dil
__sbr_cell_4_544_end:
ff_aac_sbr_decode_usac_data.L3bd8:
__sbr_cell_4_545:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_545_end:
__sbr_cell_4_546:
    mov rdi, QWORD PTR [r14+0]
__sbr_cell_4_546_end:
__sbr_cell_4_547:
    mov r8d, ecx
__sbr_cell_4_547_end:
__sbr_cell_4_548:
    shr r8d, 3
__sbr_cell_4_548_end:
__sbr_cell_4_549:
    xor r9d, r9d
__sbr_cell_4_549_end:
__sbr_cell_4_550:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_550_end:
__sbr_cell_4_551:
    setl r9b
__sbr_cell_4_551_end:
__sbr_cell_4_552:
    add r9d, ecx
__sbr_cell_4_552_end:
__sbr_cell_4_553:
    movzx edi, BYTE PTR [rdi+r8*1+0]
__sbr_cell_4_553_end:
__sbr_cell_4_554:
    and cl, 7
__sbr_cell_4_554_end:
__sbr_cell_4_555:
    shl edi, cl
__sbr_cell_4_555_end:
__sbr_cell_4_556:
    mov DWORD PTR [r14+8], r9d
__sbr_cell_4_556_end:
__sbr_cell_4_557:
    shr dil, 7
__sbr_cell_4_557_end:
__sbr_cell_4_558:
    mov BYTE PTR [rbx+rax*1+166354], dil
__sbr_cell_4_558_end:
__sbr_cell_4_559:
    add rax, 2
__sbr_cell_4_559_end:
__sbr_cell_4_560:
    cmp rsi, rax
__sbr_cell_4_560_end:
__sbr_cell_4_561:
    jne ff_aac_sbr_decode_usac_data.L3ba2
__sbr_cell_4_561_end:
__sbr_cell_4_562:
    test dl, 1
__sbr_cell_4_562_end:
__sbr_cell_4_563:
    je ff_aac_sbr_decode_usac_data.L3c4b
__sbr_cell_4_563_end:
ff_aac_sbr_decode_usac_data.L3c1c:
__sbr_cell_4_564:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_564_end:
__sbr_cell_4_565:
    mov edx, ecx
__sbr_cell_4_565_end:
__sbr_cell_4_566:
    shr edx, 3
__sbr_cell_4_566_end:
__sbr_cell_4_567:
    xor esi, esi
__sbr_cell_4_567_end:
__sbr_cell_4_568:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_568_end:
__sbr_cell_4_569:
    mov rdi, QWORD PTR [r14+0]
__sbr_cell_4_569_end:
__sbr_cell_4_570:
    setl sil
__sbr_cell_4_570_end:
__sbr_cell_4_571:
    add esi, ecx
__sbr_cell_4_571_end:
__sbr_cell_4_572:
    movzx edx, BYTE PTR [rdi+rdx*1+0]
__sbr_cell_4_572_end:
__sbr_cell_4_573:
    and cl, 7
__sbr_cell_4_573_end:
__sbr_cell_4_574:
    shl edx, cl
__sbr_cell_4_574_end:
__sbr_cell_4_575:
    mov DWORD PTR [r14+8], esi
__sbr_cell_4_575_end:
__sbr_cell_4_576:
    shr dl, 7
__sbr_cell_4_576_end:
__sbr_cell_4_577:
    mov BYTE PTR [rbx+rax*1+166353], dl
__sbr_cell_4_577_end:
ff_aac_sbr_decode_usac_data.L3c4b:
__sbr_cell_4_578:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_578_end:
__sbr_cell_4_579:
    mov rax, QWORD PTR [r14+0]
__sbr_cell_4_579_end:
__sbr_cell_4_580:
    mov edx, ecx
__sbr_cell_4_580_end:
__sbr_cell_4_581:
    shr edx, 3
__sbr_cell_4_581_end:
__sbr_cell_4_582:
    xor esi, esi
__sbr_cell_4_582_end:
__sbr_cell_4_583:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_583_end:
__sbr_cell_4_584:
    setl sil
__sbr_cell_4_584_end:
__sbr_cell_4_585:
    add esi, ecx
__sbr_cell_4_585_end:
__sbr_cell_4_586:
    movzx edx, BYTE PTR [rax+rdx*1+0]
__sbr_cell_4_586_end:
__sbr_cell_4_587:
    and cl, 7
__sbr_cell_4_587_end:
__sbr_cell_4_588:
    shl edx, cl
__sbr_cell_4_588_end:
__sbr_cell_4_589:
    shr edx, 7
__sbr_cell_4_589_end:
__sbr_cell_4_590:
    mov DWORD PTR [r14+8], esi
__sbr_cell_4_590_end:
__sbr_cell_4_591:
    xor eax, eax
__sbr_cell_4_591_end:
__sbr_cell_4_592:
    and edx, 1
__sbr_cell_4_592_end:
__sbr_cell_4_593:
    mov DWORD PTR [rbx+255076], edx
__sbr_cell_4_593_end:
__sbr_cell_4_594:
    je ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_594_end:
ff_aac_sbr_decode_usac_data.L3c84:
__sbr_cell_4_595:
    movsxd rsi, DWORD PTR [rbx+477956]
__sbr_cell_4_595_end:
__sbr_cell_4_596:
    test rsi, rsi
__sbr_cell_4_596_end:
__sbr_cell_4_597:
    jle ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_597_end:
__sbr_cell_4_598:
    xor eax, eax
__sbr_cell_4_598_end:
__sbr_cell_4_599:
    cmp esi, 1
__sbr_cell_4_599_end:
__sbr_cell_4_600:
    jne ff_aac_sbr_decode_usac_data.L3ca2
__sbr_cell_4_600_end:
ff_aac_sbr_decode_usac_data.L3c9b:
__sbr_cell_4_601:
    xor edx, edx
__sbr_cell_4_601_end:
__sbr_cell_4_602:
    jmp ff_aac_sbr_decode_usac_data.L3d2d
__sbr_cell_4_602_end:
ff_aac_sbr_decode_usac_data.L3ca2:
__sbr_cell_4_603:
    mov edi, esi
__sbr_cell_4_603_end:
__sbr_cell_4_604:
    and edi, 2147483646
__sbr_cell_4_604_end:
__sbr_cell_4_605:
    xor edx, edx
__sbr_cell_4_605_end:
ff_aac_sbr_decode_usac_data.L3cac:
__sbr_cell_4_606:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_606_end:
__sbr_cell_4_607:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_607_end:
__sbr_cell_4_608:
    mov r9d, ecx
__sbr_cell_4_608_end:
__sbr_cell_4_609:
    shr r9d, 3
__sbr_cell_4_609_end:
__sbr_cell_4_610:
    xor r10d, r10d
__sbr_cell_4_610_end:
__sbr_cell_4_611:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_611_end:
__sbr_cell_4_612:
    setl r10b
__sbr_cell_4_612_end:
__sbr_cell_4_613:
    add r10d, ecx
__sbr_cell_4_613_end:
__sbr_cell_4_614:
    movzx r8d, BYTE PTR [r8+r9*1+0]
__sbr_cell_4_614_end:
__sbr_cell_4_615:
    and cl, 7
__sbr_cell_4_615_end:
__sbr_cell_4_616:
    shl r8d, cl
__sbr_cell_4_616_end:
__sbr_cell_4_617:
    mov DWORD PTR [r14+8], r10d
__sbr_cell_4_617_end:
__sbr_cell_4_618:
    shr r8b, 7
__sbr_cell_4_618_end:
__sbr_cell_4_619:
    mov BYTE PTR [rbx+rdx*1+255121], r8b
__sbr_cell_4_619_end:
ff_aac_sbr_decode_usac_data.L3ce3:
__sbr_cell_4_620:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_620_end:
__sbr_cell_4_621:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_621_end:
__sbr_cell_4_622:
    mov r9d, ecx
__sbr_cell_4_622_end:
__sbr_cell_4_623:
    shr r9d, 3
__sbr_cell_4_623_end:
__sbr_cell_4_624:
    xor r10d, r10d
__sbr_cell_4_624_end:
__sbr_cell_4_625:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_625_end:
__sbr_cell_4_626:
    setl r10b
__sbr_cell_4_626_end:
__sbr_cell_4_627:
    add r10d, ecx
__sbr_cell_4_627_end:
__sbr_cell_4_628:
    movzx r8d, BYTE PTR [r8+r9*1+0]
__sbr_cell_4_628_end:
__sbr_cell_4_629:
    and cl, 7
__sbr_cell_4_629_end:
__sbr_cell_4_630:
    shl r8d, cl
__sbr_cell_4_630_end:
__sbr_cell_4_631:
    mov DWORD PTR [r14+8], r10d
__sbr_cell_4_631_end:
__sbr_cell_4_632:
    shr r8b, 7
__sbr_cell_4_632_end:
__sbr_cell_4_633:
    mov BYTE PTR [rbx+rdx*1+255122], r8b
__sbr_cell_4_633_end:
__sbr_cell_4_634:
    add rdx, 2
__sbr_cell_4_634_end:
__sbr_cell_4_635:
    cmp rdi, rdx
__sbr_cell_4_635_end:
__sbr_cell_4_636:
    jne ff_aac_sbr_decode_usac_data.L3cac
__sbr_cell_4_636_end:
ff_aac_sbr_decode_usac_data.L3d23:
__sbr_cell_4_637:
    test sil, 1
__sbr_cell_4_637_end:
__sbr_cell_4_638:
    je ff_aac_sbr_decode_usac_data.L36c0
__sbr_cell_4_638_end:
ff_aac_sbr_decode_usac_data.L3d2d:
__sbr_cell_4_639:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_639_end:
__sbr_cell_4_640:
    mov esi, ecx
__sbr_cell_4_640_end:
__sbr_cell_4_641:
    shr esi, 3
__sbr_cell_4_641_end:
__sbr_cell_4_642:
    xor edi, edi
__sbr_cell_4_642_end:
__sbr_cell_4_643:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_643_end:
__sbr_cell_4_644:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_644_end:
__sbr_cell_4_645:
    setl dil
__sbr_cell_4_645_end:
__sbr_cell_4_646:
    add edi, ecx
__sbr_cell_4_646_end:
__sbr_cell_4_647:
    movzx esi, BYTE PTR [r8+rsi*1+0]
__sbr_cell_4_647_end:
__sbr_cell_4_648:
    and cl, 7
__sbr_cell_4_648_end:
__sbr_cell_4_649:
    shl esi, cl
__sbr_cell_4_649_end:
__sbr_cell_4_650:
    mov DWORD PTR [r14+8], edi
__sbr_cell_4_650_end:
__sbr_cell_4_651:
    shr sil, 7
__sbr_cell_4_651_end:
__sbr_cell_4_652:
    mov BYTE PTR [rbx+rdx*1+255121], sil
__sbr_cell_4_652_end:
__sbr_cell_4_653:
    jmp ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_653_end:
ff_aac_sbr_decode_usac_data.L3d64:
__sbr_cell_4_654:
    mov esi, edx
__sbr_cell_4_654_end:
__sbr_cell_4_655:
    and esi, 2147483646
__sbr_cell_4_655_end:
__sbr_cell_4_656:
    xor eax, eax
__sbr_cell_4_656_end:
ff_aac_sbr_decode_usac_data.L3d6e:
__sbr_cell_4_657:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_657_end:
__sbr_cell_4_658:
    mov rdi, QWORD PTR [r14+0]
__sbr_cell_4_658_end:
__sbr_cell_4_659:
    mov r8d, ecx
__sbr_cell_4_659_end:
__sbr_cell_4_660:
    shr r8d, 3
__sbr_cell_4_660_end:
__sbr_cell_4_661:
    xor r9d, r9d
__sbr_cell_4_661_end:
__sbr_cell_4_662:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_662_end:
__sbr_cell_4_663:
    setl r9b
__sbr_cell_4_663_end:
__sbr_cell_4_664:
    add r9d, ecx
__sbr_cell_4_664_end:
__sbr_cell_4_665:
    movzx edi, BYTE PTR [rdi+r8*1+0]
__sbr_cell_4_665_end:
__sbr_cell_4_666:
    and cl, 7
__sbr_cell_4_666_end:
__sbr_cell_4_667:
    shl edi, cl
__sbr_cell_4_667_end:
__sbr_cell_4_668:
    mov DWORD PTR [r14+8], r9d
__sbr_cell_4_668_end:
__sbr_cell_4_669:
    shr dil, 7
__sbr_cell_4_669_end:
__sbr_cell_4_670:
    mov BYTE PTR [rbx+rax*1+166353], dil
__sbr_cell_4_670_end:
ff_aac_sbr_decode_usac_data.L3da4:
__sbr_cell_4_671:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_671_end:
__sbr_cell_4_672:
    mov rdi, QWORD PTR [r14+0]
__sbr_cell_4_672_end:
__sbr_cell_4_673:
    mov r8d, ecx
__sbr_cell_4_673_end:
__sbr_cell_4_674:
    shr r8d, 3
__sbr_cell_4_674_end:
__sbr_cell_4_675:
    xor r9d, r9d
__sbr_cell_4_675_end:
__sbr_cell_4_676:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_676_end:
__sbr_cell_4_677:
    setl r9b
__sbr_cell_4_677_end:
__sbr_cell_4_678:
    add r9d, ecx
__sbr_cell_4_678_end:
__sbr_cell_4_679:
    movzx edi, BYTE PTR [rdi+r8*1+0]
__sbr_cell_4_679_end:
__sbr_cell_4_680:
    and cl, 7
__sbr_cell_4_680_end:
__sbr_cell_4_681:
    shl edi, cl
__sbr_cell_4_681_end:
__sbr_cell_4_682:
    mov DWORD PTR [r14+8], r9d
__sbr_cell_4_682_end:
__sbr_cell_4_683:
    shr dil, 7
__sbr_cell_4_683_end:
__sbr_cell_4_684:
    mov BYTE PTR [rbx+rax*1+166354], dil
__sbr_cell_4_684_end:
__sbr_cell_4_685:
    add rax, 2
__sbr_cell_4_685_end:
__sbr_cell_4_686:
    cmp rsi, rax
__sbr_cell_4_686_end:
__sbr_cell_4_687:
    jne ff_aac_sbr_decode_usac_data.L3d6e
__sbr_cell_4_687_end:
__sbr_cell_4_688:
    test dl, 1
__sbr_cell_4_688_end:
__sbr_cell_4_689:
    je ff_aac_sbr_decode_usac_data.L3e17
__sbr_cell_4_689_end:
ff_aac_sbr_decode_usac_data.L3de8:
__sbr_cell_4_690:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_690_end:
__sbr_cell_4_691:
    mov edx, ecx
__sbr_cell_4_691_end:
__sbr_cell_4_692:
    shr edx, 3
__sbr_cell_4_692_end:
__sbr_cell_4_693:
    xor esi, esi
__sbr_cell_4_693_end:
__sbr_cell_4_694:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_694_end:
__sbr_cell_4_695:
    mov rdi, QWORD PTR [r14+0]
__sbr_cell_4_695_end:
__sbr_cell_4_696:
    setl sil
__sbr_cell_4_696_end:
__sbr_cell_4_697:
    add esi, ecx
__sbr_cell_4_697_end:
__sbr_cell_4_698:
    movzx edx, BYTE PTR [rdi+rdx*1+0]
__sbr_cell_4_698_end:
__sbr_cell_4_699:
    and cl, 7
__sbr_cell_4_699_end:
__sbr_cell_4_700:
    shl edx, cl
__sbr_cell_4_700_end:
__sbr_cell_4_701:
    mov DWORD PTR [r14+8], esi
__sbr_cell_4_701_end:
__sbr_cell_4_702:
    shr dl, 7
__sbr_cell_4_702_end:
__sbr_cell_4_703:
    mov BYTE PTR [rbx+rax*1+166353], dl
__sbr_cell_4_703_end:
ff_aac_sbr_decode_usac_data.L3e17:
__sbr_cell_4_704:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_704_end:
__sbr_cell_4_705:
    mov rax, QWORD PTR [r14+0]
__sbr_cell_4_705_end:
__sbr_cell_4_706:
    mov edx, ecx
__sbr_cell_4_706_end:
__sbr_cell_4_707:
    shr edx, 3
__sbr_cell_4_707_end:
__sbr_cell_4_708:
    xor esi, esi
__sbr_cell_4_708_end:
__sbr_cell_4_709:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_709_end:
__sbr_cell_4_710:
    setl sil
__sbr_cell_4_710_end:
__sbr_cell_4_711:
    add esi, ecx
__sbr_cell_4_711_end:
__sbr_cell_4_712:
    movzx edx, BYTE PTR [rax+rdx*1+0]
__sbr_cell_4_712_end:
__sbr_cell_4_713:
    and cl, 7
__sbr_cell_4_713_end:
__sbr_cell_4_714:
    shl edx, cl
__sbr_cell_4_714_end:
__sbr_cell_4_715:
    shr edx, 7
__sbr_cell_4_715_end:
__sbr_cell_4_716:
    mov DWORD PTR [r14+8], esi
__sbr_cell_4_716_end:
__sbr_cell_4_717:
    xor eax, eax
__sbr_cell_4_717_end:
__sbr_cell_4_718:
    and edx, 1
__sbr_cell_4_718_end:
__sbr_cell_4_719:
    mov DWORD PTR [rbx+255076], edx
__sbr_cell_4_719_end:
__sbr_cell_4_720:
    je ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_720_end:
ff_aac_sbr_decode_usac_data.L3e50:
__sbr_cell_4_721:
    movsxd rsi, DWORD PTR [rbx+477956]
__sbr_cell_4_721_end:
__sbr_cell_4_722:
    test rsi, rsi
__sbr_cell_4_722_end:
__sbr_cell_4_723:
    jle ff_aac_sbr_decode_usac_data.L3ef1
__sbr_cell_4_723_end:
__sbr_cell_4_724:
    xor eax, eax
__sbr_cell_4_724_end:
__sbr_cell_4_725:
    cmp esi, 1
__sbr_cell_4_725_end:
__sbr_cell_4_726:
    je ff_aac_sbr_decode_usac_data.L3c9b
__sbr_cell_4_726_end:
__sbr_cell_4_727:
    mov edi, esi
__sbr_cell_4_727_end:
__sbr_cell_4_728:
    and edi, 2147483646
__sbr_cell_4_728_end:
__sbr_cell_4_729:
    xor edx, edx
__sbr_cell_4_729_end:
ff_aac_sbr_decode_usac_data.L3e75:
__sbr_cell_4_730:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_730_end:
__sbr_cell_4_731:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_731_end:
__sbr_cell_4_732:
    mov r9d, ecx
__sbr_cell_4_732_end:
__sbr_cell_4_733:
    shr r9d, 3
__sbr_cell_4_733_end:
__sbr_cell_4_734:
    xor r10d, r10d
__sbr_cell_4_734_end:
__sbr_cell_4_735:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_735_end:
__sbr_cell_4_736:
    setl r10b
__sbr_cell_4_736_end:
__sbr_cell_4_737:
    add r10d, ecx
__sbr_cell_4_737_end:
__sbr_cell_4_738:
    movzx r8d, BYTE PTR [r8+r9*1+0]
__sbr_cell_4_738_end:
__sbr_cell_4_739:
    and cl, 7
__sbr_cell_4_739_end:
__sbr_cell_4_740:
    shl r8d, cl
__sbr_cell_4_740_end:
__sbr_cell_4_741:
    mov DWORD PTR [r14+8], r10d
__sbr_cell_4_741_end:
__sbr_cell_4_742:
    shr r8b, 7
__sbr_cell_4_742_end:
__sbr_cell_4_743:
    mov BYTE PTR [rbx+rdx*1+255121], r8b
__sbr_cell_4_743_end:
ff_aac_sbr_decode_usac_data.L3eac:
__sbr_cell_4_744:
    mov ecx, DWORD PTR [r14+8]
__sbr_cell_4_744_end:
__sbr_cell_4_745:
    mov r8, QWORD PTR [r14+0]
__sbr_cell_4_745_end:
__sbr_cell_4_746:
    mov r9d, ecx
__sbr_cell_4_746_end:
__sbr_cell_4_747:
    shr r9d, 3
__sbr_cell_4_747_end:
__sbr_cell_4_748:
    xor r10d, r10d
__sbr_cell_4_748_end:
__sbr_cell_4_749:
    cmp ecx, DWORD PTR [r14+16]
__sbr_cell_4_749_end:
__sbr_cell_4_750:
    setl r10b
__sbr_cell_4_750_end:
__sbr_cell_4_751:
    add r10d, ecx
__sbr_cell_4_751_end:
__sbr_cell_4_752:
    movzx r8d, BYTE PTR [r8+r9*1+0]
__sbr_cell_4_752_end:
__sbr_cell_4_753:
    and cl, 7
__sbr_cell_4_753_end:
__sbr_cell_4_754:
    shl r8d, cl
__sbr_cell_4_754_end:
__sbr_cell_4_755:
    mov DWORD PTR [r14+8], r10d
__sbr_cell_4_755_end:
__sbr_cell_4_756:
    shr r8b, 7
__sbr_cell_4_756_end:
__sbr_cell_4_757:
    mov BYTE PTR [rbx+rdx*1+255122], r8b
__sbr_cell_4_757_end:
__sbr_cell_4_758:
    add rdx, 2
__sbr_cell_4_758_end:
__sbr_cell_4_759:
    cmp rdi, rdx
__sbr_cell_4_759_end:
__sbr_cell_4_760:
    jne ff_aac_sbr_decode_usac_data.L3e75
__sbr_cell_4_760_end:
__sbr_cell_4_761:
    jmp ff_aac_sbr_decode_usac_data.L3d23
__sbr_cell_4_761_end:
ff_aac_sbr_decode_usac_data.L3ef1:
__sbr_cell_4_762:
    add rsp, 24
__sbr_cell_4_762_end:
__sbr_cell_4_763:
    pop rbx
__sbr_cell_4_763_end:
__sbr_cell_4_764:
    pop r12
__sbr_cell_4_764_end:
__sbr_cell_4_765:
    pop r13
__sbr_cell_4_765_end:
__sbr_cell_4_766:
    pop r14
__sbr_cell_4_766_end:
__sbr_cell_4_767:
    pop r15
__sbr_cell_4_767_end:
__sbr_cell_4_768:
    pop rbp
__sbr_cell_4_768_end:
ff_aac_sbr_decode_usac_data.done:
__sbr_cell_4_769:
    ret
__sbr_cell_4_769_end:
ff_aac_sbr_decode_usac_data.L3f00:
__sbr_cell_4_770:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_4_770_end:
__sbr_cell_4_771:
    int3
__sbr_cell_4_771_end:
__sbr_cell_4_772:
    int3
__sbr_cell_4_772_end:
__sbr_cell_4_773:
    int3
__sbr_cell_4_773_end:
__sbr_cell_4_774:
    int3
__sbr_cell_4_774_end:
__sbr_cell_4_775:
    int3
__sbr_cell_4_775_end:
__sbr_cell_4_776:
    int3
__sbr_cell_4_776_end:
__sbr_cell_4_777:
    int3
__sbr_cell_4_777_end:
__sbr_cell_4_778:
    int3
__sbr_cell_4_778_end:
__sbr_cell_4_779:
    int3
__sbr_cell_4_779_end:
__sbr_cell_4_780:
    int3
__sbr_cell_4_780_end:
__sbr_cell_4_781:
    int3
__sbr_cell_4_781_end:
.size ff_aac_sbr_decode_usac_data, .-ff_aac_sbr_decode_usac_data
.section .text.ff_ps_read_data,"ax",@progbits
.globl ff_ps_read_data
.type ff_ps_read_data,@function
ff_ps_read_data:
__sbr_cell_5_0:
    push rbp
__sbr_cell_5_0_end:
__sbr_cell_5_1:
    mov rbp, rsp
__sbr_cell_5_1_end:
__sbr_cell_5_2:
    push r15
__sbr_cell_5_2_end:
__sbr_cell_5_3:
    push r14
__sbr_cell_5_3_end:
__sbr_cell_5_4:
    push r13
__sbr_cell_5_4_end:
__sbr_cell_5_5:
    push r12
__sbr_cell_5_5_end:
__sbr_cell_5_6:
    push rbx
__sbr_cell_5_6_end:
__sbr_cell_5_7:
    sub rsp, 120
__sbr_cell_5_7_end:
ff_ps_read_data.L11:
__sbr_cell_5_8:
    mov DWORD PTR [rbp-44], ecx
__sbr_cell_5_8_end:
__sbr_cell_5_9:
    mov rbx, rdx
__sbr_cell_5_9_end:
__sbr_cell_5_10:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_5_10_end:
__sbr_cell_5_11:
    mov r13, QWORD PTR [rsi+0]
__sbr_cell_5_11_end:
__sbr_cell_5_12:
    mov r12d, DWORD PTR [rsi+16]
__sbr_cell_5_12_end:
__sbr_cell_5_13:
    mov eax, ecx
__sbr_cell_5_13_end:
__sbr_cell_5_14:
    shr eax, 3
__sbr_cell_5_14_end:
__sbr_cell_5_15:
    movzx edx, BYTE PTR [r13+rax*1+0]
__sbr_cell_5_15_end:
ff_ps_read_data.L2c:
__sbr_cell_5_16:
    xor eax, eax
__sbr_cell_5_16_end:
__sbr_cell_5_17:
    cmp ecx, r12d
__sbr_cell_5_17_end:
__sbr_cell_5_18:
    setl al
__sbr_cell_5_18_end:
__sbr_cell_5_19:
    add eax, ecx
__sbr_cell_5_19_end:
__sbr_cell_5_20:
    mov DWORD PTR [rbp-140], ecx
__sbr_cell_5_20_end:
ff_ps_read_data.L3c:
__sbr_cell_5_21:
    and cl, 7
__sbr_cell_5_21_end:
__sbr_cell_5_22:
    mov r8d, 128
__sbr_cell_5_22_end:
__sbr_cell_5_23:
    shr r8d, cl
__sbr_cell_5_23_end:
__sbr_cell_5_24:
    and r8d, edx
__sbr_cell_5_24_end:
__sbr_cell_5_25:
    mov DWORD PTR [rbp-136], r8d
__sbr_cell_5_25_end:
__sbr_cell_5_26:
    mov QWORD PTR [rbp-152], rsi
__sbr_cell_5_26_end:
__sbr_cell_5_27:
    je ff_ps_read_data.Lb6
__sbr_cell_5_27_end:
ff_ps_read_data.L5b:
__sbr_cell_5_28:
    mov ecx, eax
__sbr_cell_5_28_end:
__sbr_cell_5_29:
    shr ecx, 3
__sbr_cell_5_29_end:
__sbr_cell_5_30:
    xor edx, edx
__sbr_cell_5_30_end:
__sbr_cell_5_31:
    cmp eax, r12d
__sbr_cell_5_31_end:
__sbr_cell_5_32:
    setl dl
__sbr_cell_5_32_end:
__sbr_cell_5_33:
    add edx, eax
__sbr_cell_5_33_end:
__sbr_cell_5_34:
    movzx r8d, BYTE PTR [r13+rcx*1+0]
__sbr_cell_5_34_end:
ff_ps_read_data.L70:
__sbr_cell_5_35:
    and al, 7
__sbr_cell_5_35_end:
__sbr_cell_5_36:
    mov ecx, eax
__sbr_cell_5_36_end:
__sbr_cell_5_37:
    shl r8d, cl
__sbr_cell_5_37_end:
__sbr_cell_5_38:
    shr r8d, 7
__sbr_cell_5_38_end:
__sbr_cell_5_39:
    and r8d, 1
__sbr_cell_5_39_end:
__sbr_cell_5_40:
    mov DWORD PTR [rbx+4], r8d
__sbr_cell_5_40_end:
__sbr_cell_5_41:
    je ff_ps_read_data.Lf3
__sbr_cell_5_41_end:
ff_ps_read_data.L85:
__sbr_cell_5_42:
    mov eax, edx
__sbr_cell_5_42_end:
__sbr_cell_5_43:
    shr eax, 3
__sbr_cell_5_43_end:
__sbr_cell_5_44:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_44_end:
__sbr_cell_5_45:
    bswap eax
__sbr_cell_5_45_end:
__sbr_cell_5_46:
    mov ecx, edx
__sbr_cell_5_46_end:
__sbr_cell_5_47:
    and cl, 7
__sbr_cell_5_47_end:
__sbr_cell_5_48:
    shl eax, cl
__sbr_cell_5_48_end:
__sbr_cell_5_49:
    shr eax, 29
__sbr_cell_5_49_end:
__sbr_cell_5_50:
    add edx, 3
__sbr_cell_5_50_end:
__sbr_cell_5_51:
    cmp r12d, edx
__sbr_cell_5_51_end:
__sbr_cell_5_52:
    cmovb edx, r12d
__sbr_cell_5_52_end:
__sbr_cell_5_53:
    cmp eax, 5
__sbr_cell_5_53_end:
__sbr_cell_5_54:
    jle ff_ps_read_data.Lbf
__sbr_cell_5_54_end:
ff_ps_read_data.Laa:
__sbr_cell_5_55:
    lea rdx, [rip+L_str]
__sbr_cell_5_55_end:
__sbr_cell_5_56:
    jmp ff_ps_read_data.L1464
__sbr_cell_5_56_end:
ff_ps_read_data.Lb6:
__sbr_cell_5_57:
    mov QWORD PTR [rbp-64], rdi
__sbr_cell_5_57_end:
__sbr_cell_5_58:
    jmp ff_ps_read_data.L197
__sbr_cell_5_58_end:
ff_ps_read_data.Lbf:
__sbr_cell_5_59:
    ja ff_ps_read_data.L17a9
__sbr_cell_5_59_end:
__sbr_cell_5_60:
    mov ecx, eax
__sbr_cell_5_60_end:
__sbr_cell_5_61:
    lea r8, [rip+nr_iidicc_par_tab]
__sbr_cell_5_61_end:
__sbr_cell_5_62:
    movsx r8d, BYTE PTR [rcx+r8*1+0]
__sbr_cell_5_62_end:
__sbr_cell_5_63:
    mov DWORD PTR [rbx+12], r8d
__sbr_cell_5_63_end:
ff_ps_read_data.Ld7:
__sbr_cell_5_64:
    xor r8d, r8d
__sbr_cell_5_64_end:
__sbr_cell_5_65:
    cmp eax, 3
__sbr_cell_5_65_end:
__sbr_cell_5_66:
    setae r8b
__sbr_cell_5_66_end:
__sbr_cell_5_67:
    mov DWORD PTR [rbx+8], r8d
__sbr_cell_5_67_end:
__sbr_cell_5_68:
    lea rax, [rip+nr_iidopd_par_tab]
__sbr_cell_5_68_end:
__sbr_cell_5_69:
    movsx eax, BYTE PTR [rcx+rax*1+0]
__sbr_cell_5_69_end:
__sbr_cell_5_70:
    mov DWORD PTR [rbx+16], eax
__sbr_cell_5_70_end:
ff_ps_read_data.Lf3:
__sbr_cell_5_71:
    mov eax, edx
__sbr_cell_5_71_end:
__sbr_cell_5_72:
    shr eax, 3
__sbr_cell_5_72_end:
__sbr_cell_5_73:
    xor r8d, r8d
__sbr_cell_5_73_end:
__sbr_cell_5_74:
    cmp edx, r12d
__sbr_cell_5_74_end:
__sbr_cell_5_75:
    setl r8b
__sbr_cell_5_75_end:
__sbr_cell_5_76:
    add r8d, edx
__sbr_cell_5_76_end:
__sbr_cell_5_77:
    movzx eax, BYTE PTR [r13+rax*1+0]
__sbr_cell_5_77_end:
ff_ps_read_data.L10b:
__sbr_cell_5_78:
    and dl, 7
__sbr_cell_5_78_end:
__sbr_cell_5_79:
    mov ecx, edx
__sbr_cell_5_79_end:
__sbr_cell_5_80:
    shl eax, cl
__sbr_cell_5_80_end:
__sbr_cell_5_81:
    shr eax, 7
__sbr_cell_5_81_end:
__sbr_cell_5_82:
    and eax, 1
__sbr_cell_5_82_end:
__sbr_cell_5_83:
    mov DWORD PTR [rbx+20], eax
__sbr_cell_5_83_end:
__sbr_cell_5_84:
    je ff_ps_read_data.L16a
__sbr_cell_5_84_end:
ff_ps_read_data.L11d:
__sbr_cell_5_85:
    mov eax, r8d
__sbr_cell_5_85_end:
__sbr_cell_5_86:
    shr eax, 3
__sbr_cell_5_86_end:
__sbr_cell_5_87:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_87_end:
__sbr_cell_5_88:
    bswap eax
__sbr_cell_5_88_end:
__sbr_cell_5_89:
    mov ecx, r8d
__sbr_cell_5_89_end:
__sbr_cell_5_90:
    and cl, 7
__sbr_cell_5_90_end:
__sbr_cell_5_91:
    shl eax, cl
__sbr_cell_5_91_end:
__sbr_cell_5_92:
    shr eax, 29
__sbr_cell_5_92_end:
ff_ps_read_data.L135:
__sbr_cell_5_93:
    add r8d, 3
__sbr_cell_5_93_end:
__sbr_cell_5_94:
    cmp r12d, r8d
__sbr_cell_5_94_end:
__sbr_cell_5_95:
    cmovb r8d, r12d
__sbr_cell_5_95_end:
__sbr_cell_5_96:
    mov DWORD PTR [rbx+24], eax
__sbr_cell_5_96_end:
__sbr_cell_5_97:
    cmp eax, 6
__sbr_cell_5_97_end:
__sbr_cell_5_98:
    jl ff_ps_read_data.L154
__sbr_cell_5_98_end:
ff_ps_read_data.L148:
__sbr_cell_5_99:
    lea rdx, [rip+L_str_1]
__sbr_cell_5_99_end:
__sbr_cell_5_100:
    jmp ff_ps_read_data.L1464
__sbr_cell_5_100_end:
ff_ps_read_data.L154:
__sbr_cell_5_101:
    jae ff_ps_read_data.L17ae
__sbr_cell_5_101_end:
__sbr_cell_5_102:
    mov eax, eax
__sbr_cell_5_102_end:
__sbr_cell_5_103:
    lea rcx, [rip+nr_iidicc_par_tab]
__sbr_cell_5_103_end:
__sbr_cell_5_104:
    movsx eax, BYTE PTR [rax+rcx*1+0]
__sbr_cell_5_104_end:
__sbr_cell_5_105:
    mov DWORD PTR [rbx+28], eax
__sbr_cell_5_105_end:
ff_ps_read_data.L16a:
__sbr_cell_5_106:
    mov QWORD PTR [rbp-64], rdi
__sbr_cell_5_106_end:
__sbr_cell_5_107:
    mov ecx, r8d
__sbr_cell_5_107_end:
__sbr_cell_5_108:
    shr ecx, 3
__sbr_cell_5_108_end:
__sbr_cell_5_109:
    xor eax, eax
__sbr_cell_5_109_end:
__sbr_cell_5_110:
    cmp r8d, r12d
__sbr_cell_5_110_end:
__sbr_cell_5_111:
    setl al
__sbr_cell_5_111_end:
__sbr_cell_5_112:
    add eax, r8d
__sbr_cell_5_112_end:
__sbr_cell_5_113:
    movzx edx, BYTE PTR [r13+rcx*1+0]
__sbr_cell_5_113_end:
ff_ps_read_data.L185:
__sbr_cell_5_114:
    and r8b, 7
__sbr_cell_5_114_end:
__sbr_cell_5_115:
    mov ecx, r8d
__sbr_cell_5_115_end:
__sbr_cell_5_116:
    shl edx, cl
__sbr_cell_5_116_end:
__sbr_cell_5_117:
    shr edx, 7
__sbr_cell_5_117_end:
__sbr_cell_5_118:
    and edx, 1
__sbr_cell_5_118_end:
__sbr_cell_5_119:
    mov DWORD PTR [rbx+32], edx
__sbr_cell_5_119_end:
ff_ps_read_data.L197:
__sbr_cell_5_120:
    mov ecx, eax
__sbr_cell_5_120_end:
__sbr_cell_5_121:
    shr ecx, 3
__sbr_cell_5_121_end:
__sbr_cell_5_122:
    xor edi, edi
__sbr_cell_5_122_end:
__sbr_cell_5_123:
    cmp eax, r12d
__sbr_cell_5_123_end:
__sbr_cell_5_124:
    setl dil
__sbr_cell_5_124_end:
__sbr_cell_5_125:
    lea edx, [rax+rdi*1+0]
__sbr_cell_5_125_end:
__sbr_cell_5_126:
    movzx esi, BYTE PTR [r13+rcx*1+0]
__sbr_cell_5_126_end:
__sbr_cell_5_127:
    mov ecx, eax
__sbr_cell_5_127_end:
ff_ps_read_data.L1b0:
__sbr_cell_5_128:
    and cl, 7
__sbr_cell_5_128_end:
__sbr_cell_5_129:
    shl esi, cl
__sbr_cell_5_129_end:
__sbr_cell_5_130:
    shr esi, 7
__sbr_cell_5_130_end:
__sbr_cell_5_131:
    and esi, 1
__sbr_cell_5_131_end:
__sbr_cell_5_132:
    mov DWORD PTR [rbx+36], esi
__sbr_cell_5_132_end:
ff_ps_read_data.L1be:
__sbr_cell_5_133:
    mov ecx, DWORD PTR [rbx+44]
__sbr_cell_5_133_end:
__sbr_cell_5_134:
    mov QWORD PTR [rbp-104], rcx
__sbr_cell_5_134_end:
__sbr_cell_5_135:
    mov DWORD PTR [rbx+40], ecx
__sbr_cell_5_135_end:
ff_ps_read_data.L1c8:
__sbr_cell_5_136:
    mov ecx, edx
__sbr_cell_5_136_end:
__sbr_cell_5_137:
    shr ecx, 3
__sbr_cell_5_137_end:
__sbr_cell_5_138:
    mov r9d, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_138_end:
__sbr_cell_5_139:
    bswap r9d
__sbr_cell_5_139_end:
__sbr_cell_5_140:
    and dl, 7
__sbr_cell_5_140_end:
__sbr_cell_5_141:
    mov ecx, edx
__sbr_cell_5_141_end:
__sbr_cell_5_142:
    shl r9d, cl
__sbr_cell_5_142_end:
__sbr_cell_5_143:
    shr r9d, 30
__sbr_cell_5_143_end:
ff_ps_read_data.L1e1:
__sbr_cell_5_144:
    lea r8d, [rax+rdi*1+0]
__sbr_cell_5_144_end:
__sbr_cell_5_145:
    add r8d, 2
__sbr_cell_5_145_end:
__sbr_cell_5_146:
    cmp r12d, r8d
__sbr_cell_5_146_end:
__sbr_cell_5_147:
    cmovb r8d, r12d
__sbr_cell_5_147_end:
__sbr_cell_5_148:
    cmp r9d, 4
__sbr_cell_5_148_end:
__sbr_cell_5_149:
    jae ff_ps_read_data.L1795
__sbr_cell_5_149_end:
ff_ps_read_data.L1fa:
__sbr_cell_5_150:
    mov eax, r9d
__sbr_cell_5_150_end:
__sbr_cell_5_151:
    mov ecx, esi
__sbr_cell_5_151_end:
__sbr_cell_5_152:
    lea rdx, [rip+num_env_tab]
__sbr_cell_5_152_end:
__sbr_cell_5_153:
    lea rcx, [rdx+rcx*4+0]
__sbr_cell_5_153_end:
__sbr_cell_5_154:
    movsx eax, BYTE PTR [rax+rcx*1+0]
__sbr_cell_5_154_end:
__sbr_cell_5_155:
    movzx r10d, al
__sbr_cell_5_155_end:
__sbr_cell_5_156:
    mov QWORD PTR [rbp-72], rax
__sbr_cell_5_156_end:
ff_ps_read_data.L216:
__sbr_cell_5_157:
    mov DWORD PTR [rbx+44], eax
__sbr_cell_5_157_end:
__sbr_cell_5_158:
    mov DWORD PTR [rbx+52], 4294967295
__sbr_cell_5_158_end:
__sbr_cell_5_159:
    test esi, esi
__sbr_cell_5_159_end:
__sbr_cell_5_160:
    jne ff_ps_read_data.L26e
__sbr_cell_5_160_end:
__sbr_cell_5_161:
    test r10b, r10b
__sbr_cell_5_161_end:
__sbr_cell_5_162:
    jle ff_ps_read_data.L715
__sbr_cell_5_162_end:
ff_ps_read_data.L22d:
__sbr_cell_5_163:
    mov rcx, QWORD PTR [rbp-72]
__sbr_cell_5_163_end:
__sbr_cell_5_164:
    lea eax, [rcx-6]
__sbr_cell_5_164_end:
__sbr_cell_5_165:
    cmp eax, 4294967291
__sbr_cell_5_165_end:
__sbr_cell_5_166:
    jb ff_ps_read_data.L179f
__sbr_cell_5_166_end:
__sbr_cell_5_167:
    mov eax, ecx
__sbr_cell_5_167_end:
__sbr_cell_5_168:
    mov rcx, QWORD PTR [rip+ff_log2_tab_got]
__sbr_cell_5_168_end:
__sbr_cell_5_169:
    movzx ecx, BYTE PTR [rcx+rax*1+0]
__sbr_cell_5_169_end:
__sbr_cell_5_170:
    mov edx, 1
__sbr_cell_5_170_end:
__sbr_cell_5_171:
    cmp r10b, 4
__sbr_cell_5_171_end:
__sbr_cell_5_172:
    jb ff_ps_read_data.L6f5
__sbr_cell_5_172_end:
ff_ps_read_data.L259:
__sbr_cell_5_173:
    vmovd xmm0, ecx
__sbr_cell_5_173_end:
__sbr_cell_5_174:
    cmp BYTE PTR [rbp-72], 16
__sbr_cell_5_174_end:
__sbr_cell_5_175:
    jae ff_ps_read_data.L3aa
__sbr_cell_5_175_end:
__sbr_cell_5_176:
    xor eax, eax
__sbr_cell_5_176_end:
__sbr_cell_5_177:
    jmp ff_ps_read_data.L69c
__sbr_cell_5_177_end:
ff_ps_read_data.L26e:
__sbr_cell_5_178:
    test r10b, r10b
__sbr_cell_5_178_end:
__sbr_cell_5_179:
    jle ff_ps_read_data.L715
__sbr_cell_5_179_end:
ff_ps_read_data.L277:
__sbr_cell_5_180:
    mov eax, r8d
__sbr_cell_5_180_end:
__sbr_cell_5_181:
    shr eax, 3
__sbr_cell_5_181_end:
__sbr_cell_5_182:
    mov edx, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_182_end:
__sbr_cell_5_183:
    bswap edx
__sbr_cell_5_183_end:
__sbr_cell_5_184:
    mov ecx, r8d
__sbr_cell_5_184_end:
__sbr_cell_5_185:
    and cl, 7
__sbr_cell_5_185_end:
__sbr_cell_5_186:
    shl edx, cl
__sbr_cell_5_186_end:
__sbr_cell_5_187:
    shr edx, 27
__sbr_cell_5_187_end:
__sbr_cell_5_188:
    mov DWORD PTR [rbx+56], edx
__sbr_cell_5_188_end:
__sbr_cell_5_189:
    cmp edx, 4294967295
__sbr_cell_5_189_end:
__sbr_cell_5_190:
    jge ff_ps_read_data.L2b3
__sbr_cell_5_190_end:
ff_ps_read_data.L297:
__sbr_cell_5_191:
    lea rdx, [rip+L_str_2]
__sbr_cell_5_191_end:
__sbr_cell_5_192:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_5_192_end:
__sbr_cell_5_193:
    mov esi, 16
__sbr_cell_5_193_end:
__sbr_cell_5_194:
    xor eax, eax
__sbr_cell_5_194_end:
__sbr_cell_5_195:
    call av_log
__sbr_cell_5_195_end:
__sbr_cell_5_196:
    jmp ff_ps_read_data.L1475
__sbr_cell_5_196_end:
ff_ps_read_data.L2b3:
__sbr_cell_5_197:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_5_197_end:
__sbr_cell_5_198:
    inc eax
__sbr_cell_5_198_end:
__sbr_cell_5_199:
    add r8d, 5
__sbr_cell_5_199_end:
__sbr_cell_5_200:
    cmp r12d, r8d
__sbr_cell_5_200_end:
__sbr_cell_5_201:
    cmovb r8d, r12d
__sbr_cell_5_201_end:
__sbr_cell_5_202:
    cmp eax, 2
__sbr_cell_5_202_end:
__sbr_cell_5_203:
    je ff_ps_read_data.L715
__sbr_cell_5_203_end:
ff_ps_read_data.L2cd:
__sbr_cell_5_204:
    mov ecx, r8d
__sbr_cell_5_204_end:
__sbr_cell_5_205:
    shr ecx, 3
__sbr_cell_5_205_end:
__sbr_cell_5_206:
    mov esi, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_206_end:
__sbr_cell_5_207:
    bswap esi
__sbr_cell_5_207_end:
__sbr_cell_5_208:
    mov ecx, r8d
__sbr_cell_5_208_end:
__sbr_cell_5_209:
    and cl, 7
__sbr_cell_5_209_end:
__sbr_cell_5_210:
    shl esi, cl
__sbr_cell_5_210_end:
__sbr_cell_5_211:
    shr esi, 27
__sbr_cell_5_211_end:
__sbr_cell_5_212:
    mov DWORD PTR [rbx+60], esi
__sbr_cell_5_212_end:
__sbr_cell_5_213:
    cmp esi, edx
__sbr_cell_5_213_end:
__sbr_cell_5_214:
    jl ff_ps_read_data.L297
__sbr_cell_5_214_end:
ff_ps_read_data.L2ec:
__sbr_cell_5_215:
    add r8d, 5
__sbr_cell_5_215_end:
__sbr_cell_5_216:
    cmp r12d, r8d
__sbr_cell_5_216_end:
__sbr_cell_5_217:
    cmovb r8d, r12d
__sbr_cell_5_217_end:
__sbr_cell_5_218:
    cmp eax, 3
__sbr_cell_5_218_end:
__sbr_cell_5_219:
    je ff_ps_read_data.L715
__sbr_cell_5_219_end:
ff_ps_read_data.L300:
__sbr_cell_5_220:
    mov ecx, r8d
__sbr_cell_5_220_end:
__sbr_cell_5_221:
    shr ecx, 3
__sbr_cell_5_221_end:
__sbr_cell_5_222:
    mov edx, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_222_end:
__sbr_cell_5_223:
    bswap edx
__sbr_cell_5_223_end:
__sbr_cell_5_224:
    mov ecx, r8d
__sbr_cell_5_224_end:
__sbr_cell_5_225:
    and cl, 7
__sbr_cell_5_225_end:
__sbr_cell_5_226:
    shl edx, cl
__sbr_cell_5_226_end:
__sbr_cell_5_227:
    shr edx, 27
__sbr_cell_5_227_end:
__sbr_cell_5_228:
    mov DWORD PTR [rbx+64], edx
__sbr_cell_5_228_end:
__sbr_cell_5_229:
    cmp edx, esi
__sbr_cell_5_229_end:
__sbr_cell_5_230:
    jl ff_ps_read_data.L297
__sbr_cell_5_230_end:
ff_ps_read_data.L323:
__sbr_cell_5_231:
    add r8d, 5
__sbr_cell_5_231_end:
__sbr_cell_5_232:
    cmp r12d, r8d
__sbr_cell_5_232_end:
__sbr_cell_5_233:
    cmovb r8d, r12d
__sbr_cell_5_233_end:
__sbr_cell_5_234:
    cmp eax, 4
__sbr_cell_5_234_end:
__sbr_cell_5_235:
    je ff_ps_read_data.L715
__sbr_cell_5_235_end:
ff_ps_read_data.L337:
__sbr_cell_5_236:
    mov ecx, r8d
__sbr_cell_5_236_end:
__sbr_cell_5_237:
    shr ecx, 3
__sbr_cell_5_237_end:
__sbr_cell_5_238:
    mov esi, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_238_end:
__sbr_cell_5_239:
    bswap esi
__sbr_cell_5_239_end:
__sbr_cell_5_240:
    mov ecx, r8d
__sbr_cell_5_240_end:
__sbr_cell_5_241:
    and cl, 7
__sbr_cell_5_241_end:
__sbr_cell_5_242:
    shl esi, cl
__sbr_cell_5_242_end:
__sbr_cell_5_243:
    shr esi, 27
__sbr_cell_5_243_end:
__sbr_cell_5_244:
    mov DWORD PTR [rbx+68], esi
__sbr_cell_5_244_end:
__sbr_cell_5_245:
    cmp esi, edx
__sbr_cell_5_245_end:
__sbr_cell_5_246:
    jl ff_ps_read_data.L297
__sbr_cell_5_246_end:
ff_ps_read_data.L35a:
__sbr_cell_5_247:
    add r8d, 5
__sbr_cell_5_247_end:
__sbr_cell_5_248:
    cmp r12d, r8d
__sbr_cell_5_248_end:
__sbr_cell_5_249:
    cmovb r8d, r12d
__sbr_cell_5_249_end:
__sbr_cell_5_250:
    cmp eax, 5
__sbr_cell_5_250_end:
__sbr_cell_5_251:
    je ff_ps_read_data.L715
__sbr_cell_5_251_end:
ff_ps_read_data.L36e:
__sbr_cell_5_252:
    mov ecx, r8d
__sbr_cell_5_252_end:
__sbr_cell_5_253:
    shr ecx, 3
__sbr_cell_5_253_end:
__sbr_cell_5_254:
    mov edx, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_254_end:
__sbr_cell_5_255:
    bswap edx
__sbr_cell_5_255_end:
__sbr_cell_5_256:
    mov ecx, r8d
__sbr_cell_5_256_end:
__sbr_cell_5_257:
    and cl, 7
__sbr_cell_5_257_end:
__sbr_cell_5_258:
    shl edx, cl
__sbr_cell_5_258_end:
__sbr_cell_5_259:
    shr edx, 27
__sbr_cell_5_259_end:
__sbr_cell_5_260:
    mov DWORD PTR [rbx+72], edx
__sbr_cell_5_260_end:
__sbr_cell_5_261:
    cmp edx, esi
__sbr_cell_5_261_end:
__sbr_cell_5_262:
    jl ff_ps_read_data.L297
__sbr_cell_5_262_end:
__sbr_cell_5_263:
    add r8d, 5
__sbr_cell_5_263_end:
__sbr_cell_5_264:
    cmp r12d, r8d
__sbr_cell_5_264_end:
__sbr_cell_5_265:
    cmovb r8d, r12d
__sbr_cell_5_265_end:
__sbr_cell_5_266:
    cmp eax, 6
__sbr_cell_5_266_end:
__sbr_cell_5_267:
    je ff_ps_read_data.L715
__sbr_cell_5_267_end:
__sbr_cell_5_268:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_268_end:
ff_ps_read_data.L3aa:
__sbr_cell_5_269:
    mov eax, r10d
__sbr_cell_5_269_end:
__sbr_cell_5_270:
    vmovdqa xmm1, XMMWORD PTR [rip+LCPI0_0]
__sbr_cell_5_270_end:
__sbr_cell_5_271:
    vpsrld xmm1, xmm1, xmm0
__sbr_cell_5_271_end:
__sbr_cell_5_272:
    and eax, 112
__sbr_cell_5_272_end:
__sbr_cell_5_273:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_1]
__sbr_cell_5_273_end:
__sbr_cell_5_274:
    vpsrld xmm3, xmm2, xmm0
__sbr_cell_5_274_end:
__sbr_cell_5_275:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_2]
__sbr_cell_5_275_end:
__sbr_cell_5_276:
    vpsrld xmm4, xmm2, xmm0
__sbr_cell_5_276_end:
__sbr_cell_5_277:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_3]
__sbr_cell_5_277_end:
__sbr_cell_5_278:
    vpsrld xmm5, xmm2, xmm0
__sbr_cell_5_278_end:
__sbr_cell_5_279:
    vpcmpeqd xmm2, xmm2, xmm2
__sbr_cell_5_279_end:
__sbr_cell_5_280:
    vpaddd xmm1, xmm1, xmm2
__sbr_cell_5_280_end:
__sbr_cell_5_281:
    vpaddd xmm3, xmm3, xmm2
__sbr_cell_5_281_end:
__sbr_cell_5_282:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_282_end:
__sbr_cell_5_283:
    vmovdqu XMMWORD PTR [rbx+56], xmm1
__sbr_cell_5_283_end:
__sbr_cell_5_284:
    vmovdqu XMMWORD PTR [rbx+72], xmm3
__sbr_cell_5_284_end:
__sbr_cell_5_285:
    vmovdqu XMMWORD PTR [rbx+88], xmm4
__sbr_cell_5_285_end:
__sbr_cell_5_286:
    vpaddd xmm1, xmm5, xmm2
__sbr_cell_5_286_end:
__sbr_cell_5_287:
    vmovdqu XMMWORD PTR [rbx+104], xmm1
__sbr_cell_5_287_end:
__sbr_cell_5_288:
    cmp rax, 16
__sbr_cell_5_288_end:
__sbr_cell_5_289:
    je ff_ps_read_data.L689
__sbr_cell_5_289_end:
__sbr_cell_5_290:
    vpmovzxdq xmm1, xmm0
__sbr_cell_5_290_end:
__sbr_cell_5_291:
    vmovdqa xmm3, XMMWORD PTR [rip+LCPI0_4]
__sbr_cell_5_291_end:
__sbr_cell_5_292:
    vpsrld xmm3, xmm3, xmm1
__sbr_cell_5_292_end:
__sbr_cell_5_293:
    vmovdqa xmm4, XMMWORD PTR [rip+LCPI0_5]
__sbr_cell_5_293_end:
__sbr_cell_5_294:
    vpsrld xmm4, xmm4, xmm1
__sbr_cell_5_294_end:
__sbr_cell_5_295:
    vmovdqa xmm5, XMMWORD PTR [rip+LCPI0_6]
__sbr_cell_5_295_end:
__sbr_cell_5_296:
    vpsrld xmm5, xmm5, xmm1
__sbr_cell_5_296_end:
__sbr_cell_5_297:
    vmovdqa xmm6, XMMWORD PTR [rip+LCPI0_7]
__sbr_cell_5_297_end:
__sbr_cell_5_298:
    vpsrld xmm6, xmm6, xmm1
__sbr_cell_5_298_end:
__sbr_cell_5_299:
    vpaddd xmm3, xmm3, xmm2
__sbr_cell_5_299_end:
__sbr_cell_5_300:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_300_end:
__sbr_cell_5_301:
    vpaddd xmm5, xmm5, xmm2
__sbr_cell_5_301_end:
__sbr_cell_5_302:
    vmovdqu XMMWORD PTR [rbx+120], xmm3
__sbr_cell_5_302_end:
__sbr_cell_5_303:
    vmovdqu XMMWORD PTR [rbx+136], xmm4
__sbr_cell_5_303_end:
__sbr_cell_5_304:
    vmovdqu XMMWORD PTR [rbx+152], xmm5
__sbr_cell_5_304_end:
__sbr_cell_5_305:
    vpaddd xmm2, xmm6, xmm2
__sbr_cell_5_305_end:
__sbr_cell_5_306:
    vmovdqu XMMWORD PTR [rbx+168], xmm2
__sbr_cell_5_306_end:
__sbr_cell_5_307:
    cmp eax, 32
__sbr_cell_5_307_end:
__sbr_cell_5_308:
    je ff_ps_read_data.L689
__sbr_cell_5_308_end:
__sbr_cell_5_309:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_8]
__sbr_cell_5_309_end:
__sbr_cell_5_310:
    vpsrld xmm3, xmm2, xmm1
__sbr_cell_5_310_end:
__sbr_cell_5_311:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_9]
__sbr_cell_5_311_end:
__sbr_cell_5_312:
    vpsrld xmm4, xmm2, xmm1
__sbr_cell_5_312_end:
__sbr_cell_5_313:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_10]
__sbr_cell_5_313_end:
__sbr_cell_5_314:
    vpsrld xmm5, xmm2, xmm1
__sbr_cell_5_314_end:
__sbr_cell_5_315:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_11]
__sbr_cell_5_315_end:
__sbr_cell_5_316:
    vpsrld xmm6, xmm2, xmm1
__sbr_cell_5_316_end:
__sbr_cell_5_317:
    vpcmpeqd xmm2, xmm2, xmm2
__sbr_cell_5_317_end:
__sbr_cell_5_318:
    vpaddd xmm3, xmm3, xmm2
__sbr_cell_5_318_end:
__sbr_cell_5_319:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_319_end:
__sbr_cell_5_320:
    vpaddd xmm5, xmm5, xmm2
__sbr_cell_5_320_end:
__sbr_cell_5_321:
    vmovdqu XMMWORD PTR [rbx+184], xmm3
__sbr_cell_5_321_end:
__sbr_cell_5_322:
    vmovdqu XMMWORD PTR [rbx+200], xmm4
__sbr_cell_5_322_end:
__sbr_cell_5_323:
    vmovdqu XMMWORD PTR [rbx+216], xmm5
__sbr_cell_5_323_end:
__sbr_cell_5_324:
    vpaddd xmm3, xmm6, xmm2
__sbr_cell_5_324_end:
__sbr_cell_5_325:
    vmovdqu XMMWORD PTR [rbx+232], xmm3
__sbr_cell_5_325_end:
__sbr_cell_5_326:
    cmp eax, 48
__sbr_cell_5_326_end:
__sbr_cell_5_327:
    je ff_ps_read_data.L689
__sbr_cell_5_327_end:
__sbr_cell_5_328:
    vmovdqa xmm3, XMMWORD PTR [rip+LCPI0_12]
__sbr_cell_5_328_end:
__sbr_cell_5_329:
    vpsrld xmm3, xmm3, xmm1
__sbr_cell_5_329_end:
__sbr_cell_5_330:
    vmovdqa xmm4, XMMWORD PTR [rip+LCPI0_13]
__sbr_cell_5_330_end:
__sbr_cell_5_331:
    vpsrld xmm4, xmm4, xmm1
__sbr_cell_5_331_end:
__sbr_cell_5_332:
    vmovdqa xmm5, XMMWORD PTR [rip+LCPI0_14]
__sbr_cell_5_332_end:
__sbr_cell_5_333:
    vpsrld xmm5, xmm5, xmm1
__sbr_cell_5_333_end:
__sbr_cell_5_334:
    vmovdqa xmm6, XMMWORD PTR [rip+LCPI0_15]
__sbr_cell_5_334_end:
__sbr_cell_5_335:
    vpsrld xmm6, xmm6, xmm1
__sbr_cell_5_335_end:
__sbr_cell_5_336:
    vpaddd xmm3, xmm3, xmm2
__sbr_cell_5_336_end:
__sbr_cell_5_337:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_337_end:
__sbr_cell_5_338:
    vpaddd xmm5, xmm5, xmm2
__sbr_cell_5_338_end:
__sbr_cell_5_339:
    vmovdqu XMMWORD PTR [rbx+248], xmm3
__sbr_cell_5_339_end:
__sbr_cell_5_340:
    vmovdqu XMMWORD PTR [rbx+264], xmm4
__sbr_cell_5_340_end:
__sbr_cell_5_341:
    vmovdqu XMMWORD PTR [rbx+280], xmm5
__sbr_cell_5_341_end:
__sbr_cell_5_342:
    vpaddd xmm2, xmm6, xmm2
__sbr_cell_5_342_end:
__sbr_cell_5_343:
    vmovdqu XMMWORD PTR [rbx+296], xmm2
__sbr_cell_5_343_end:
__sbr_cell_5_344:
    cmp eax, 64
__sbr_cell_5_344_end:
__sbr_cell_5_345:
    je ff_ps_read_data.L689
__sbr_cell_5_345_end:
__sbr_cell_5_346:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_16]
__sbr_cell_5_346_end:
__sbr_cell_5_347:
    vpsrld xmm3, xmm2, xmm1
__sbr_cell_5_347_end:
__sbr_cell_5_348:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_17]
__sbr_cell_5_348_end:
__sbr_cell_5_349:
    vpsrld xmm4, xmm2, xmm1
__sbr_cell_5_349_end:
__sbr_cell_5_350:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_18]
__sbr_cell_5_350_end:
__sbr_cell_5_351:
    vpsrld xmm5, xmm2, xmm1
__sbr_cell_5_351_end:
__sbr_cell_5_352:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_19]
__sbr_cell_5_352_end:
__sbr_cell_5_353:
    vpsrld xmm6, xmm2, xmm1
__sbr_cell_5_353_end:
__sbr_cell_5_354:
    vpcmpeqd xmm2, xmm2, xmm2
__sbr_cell_5_354_end:
__sbr_cell_5_355:
    vpaddd xmm3, xmm3, xmm2
__sbr_cell_5_355_end:
__sbr_cell_5_356:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_356_end:
__sbr_cell_5_357:
    vpaddd xmm5, xmm5, xmm2
__sbr_cell_5_357_end:
__sbr_cell_5_358:
    vmovdqu XMMWORD PTR [rbx+312], xmm3
__sbr_cell_5_358_end:
__sbr_cell_5_359:
    vmovdqu XMMWORD PTR [rbx+328], xmm4
__sbr_cell_5_359_end:
__sbr_cell_5_360:
    vmovdqu XMMWORD PTR [rbx+344], xmm5
__sbr_cell_5_360_end:
__sbr_cell_5_361:
    vpaddd xmm3, xmm6, xmm2
__sbr_cell_5_361_end:
__sbr_cell_5_362:
    vmovdqu XMMWORD PTR [rbx+360], xmm3
__sbr_cell_5_362_end:
__sbr_cell_5_363:
    cmp eax, 80
__sbr_cell_5_363_end:
__sbr_cell_5_364:
    je ff_ps_read_data.L689
__sbr_cell_5_364_end:
__sbr_cell_5_365:
    vmovdqa xmm3, XMMWORD PTR [rip+LCPI0_20]
__sbr_cell_5_365_end:
__sbr_cell_5_366:
    vpsrld xmm3, xmm3, xmm1
__sbr_cell_5_366_end:
__sbr_cell_5_367:
    vmovdqa xmm4, XMMWORD PTR [rip+LCPI0_21]
__sbr_cell_5_367_end:
__sbr_cell_5_368:
    vpsrld xmm4, xmm4, xmm1
__sbr_cell_5_368_end:
__sbr_cell_5_369:
    vmovdqa xmm5, XMMWORD PTR [rip+LCPI0_22]
__sbr_cell_5_369_end:
__sbr_cell_5_370:
    vpsrld xmm5, xmm5, xmm1
__sbr_cell_5_370_end:
__sbr_cell_5_371:
    vmovdqa xmm6, XMMWORD PTR [rip+LCPI0_23]
__sbr_cell_5_371_end:
__sbr_cell_5_372:
    vpsrld xmm6, xmm6, xmm1
__sbr_cell_5_372_end:
__sbr_cell_5_373:
    vpaddd xmm3, xmm3, xmm2
__sbr_cell_5_373_end:
__sbr_cell_5_374:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_374_end:
__sbr_cell_5_375:
    vpaddd xmm5, xmm5, xmm2
__sbr_cell_5_375_end:
__sbr_cell_5_376:
    vmovdqu XMMWORD PTR [rbx+376], xmm3
__sbr_cell_5_376_end:
__sbr_cell_5_377:
    vmovdqu XMMWORD PTR [rbx+392], xmm4
__sbr_cell_5_377_end:
__sbr_cell_5_378:
    vmovdqu XMMWORD PTR [rbx+408], xmm5
__sbr_cell_5_378_end:
__sbr_cell_5_379:
    vpaddd xmm2, xmm6, xmm2
__sbr_cell_5_379_end:
__sbr_cell_5_380:
    vmovdqu XMMWORD PTR [rbx+424], xmm2
__sbr_cell_5_380_end:
__sbr_cell_5_381:
    cmp eax, 96
__sbr_cell_5_381_end:
__sbr_cell_5_382:
    je ff_ps_read_data.L689
__sbr_cell_5_382_end:
__sbr_cell_5_383:
    vmovdqa xmm2, XMMWORD PTR [rip+LCPI0_24]
__sbr_cell_5_383_end:
__sbr_cell_5_384:
    vpsrld xmm2, xmm2, xmm1
__sbr_cell_5_384_end:
__sbr_cell_5_385:
    vmovdqa xmm3, XMMWORD PTR [rip+LCPI0_25]
__sbr_cell_5_385_end:
__sbr_cell_5_386:
    vpsrld xmm3, xmm3, xmm1
__sbr_cell_5_386_end:
__sbr_cell_5_387:
    vmovdqa xmm4, XMMWORD PTR [rip+LCPI0_26]
__sbr_cell_5_387_end:
__sbr_cell_5_388:
    vpsrld xmm4, xmm4, xmm1
__sbr_cell_5_388_end:
__sbr_cell_5_389:
    vmovdqa xmm5, XMMWORD PTR [rip+LCPI0_27]
__sbr_cell_5_389_end:
__sbr_cell_5_390:
    vpsrld xmm1, xmm5, xmm1
__sbr_cell_5_390_end:
__sbr_cell_5_391:
    vpcmpeqd xmm5, xmm5, xmm5
__sbr_cell_5_391_end:
__sbr_cell_5_392:
    vpaddd xmm2, xmm2, xmm5
__sbr_cell_5_392_end:
__sbr_cell_5_393:
    vpaddd xmm3, xmm3, xmm5
__sbr_cell_5_393_end:
__sbr_cell_5_394:
    vpaddd xmm4, xmm4, xmm5
__sbr_cell_5_394_end:
__sbr_cell_5_395:
    vpaddd xmm1, xmm1, xmm5
__sbr_cell_5_395_end:
__sbr_cell_5_396:
    vmovdqu XMMWORD PTR [rbx+440], xmm2
__sbr_cell_5_396_end:
__sbr_cell_5_397:
    vmovdqu XMMWORD PTR [rbx+456], xmm3
__sbr_cell_5_397_end:
__sbr_cell_5_398:
    vmovdqu XMMWORD PTR [rbx+472], xmm4
__sbr_cell_5_398_end:
__sbr_cell_5_399:
    vmovdqu XMMWORD PTR [rbx+488], xmm1
__sbr_cell_5_399_end:
ff_ps_read_data.L689:
__sbr_cell_5_400:
    cmp eax, r10d
__sbr_cell_5_400_end:
__sbr_cell_5_401:
    je ff_ps_read_data.L715
__sbr_cell_5_401_end:
__sbr_cell_5_402:
    lea rdx, [rax+1]
__sbr_cell_5_402_end:
__sbr_cell_5_403:
    test r10b, 12
__sbr_cell_5_403_end:
__sbr_cell_5_404:
    je ff_ps_read_data.L6f5
__sbr_cell_5_404_end:
ff_ps_read_data.L69c:
__sbr_cell_5_405:
    mov esi, r10d
__sbr_cell_5_405_end:
__sbr_cell_5_406:
    and esi, 124
__sbr_cell_5_406_end:
__sbr_cell_5_407:
    vmovd xmm1, edx
__sbr_cell_5_407_end:
__sbr_cell_5_408:
    vpshufd xmm1, xmm1, 0
__sbr_cell_5_408_end:
__sbr_cell_5_409:
    vpaddd xmm1, xmm1, XMMWORD PTR [rip+LCPI0_28]
__sbr_cell_5_409_end:
__sbr_cell_5_410:
    lea rdx, [rsi+1]
__sbr_cell_5_410_end:
__sbr_cell_5_411:
    vpmovzxdq xmm0, xmm0
__sbr_cell_5_411_end:
__sbr_cell_5_412:
    vpcmpeqd xmm2, xmm2, xmm2
__sbr_cell_5_412_end:
__sbr_cell_5_413:
    vbroadcastss xmm3, DWORD PTR [rip+LCPI0_30]
__sbr_cell_5_413_end:
__sbr_cell_5_414:
    .nops 1
__sbr_cell_5_414_end:
ff_ps_read_data.L6d0:
__sbr_cell_5_415:
    vpslld xmm4, xmm1, 5
__sbr_cell_5_415_end:
__sbr_cell_5_416:
    vpsrld xmm4, xmm4, xmm0
__sbr_cell_5_416_end:
__sbr_cell_5_417:
    vpaddd xmm4, xmm4, xmm2
__sbr_cell_5_417_end:
__sbr_cell_5_418:
    vmovdqu XMMWORD PTR [rbx+rax*4+56], xmm4
__sbr_cell_5_418_end:
__sbr_cell_5_419:
    add rax, 4
__sbr_cell_5_419_end:
__sbr_cell_5_420:
    vpaddd xmm1, xmm1, xmm3
__sbr_cell_5_420_end:
__sbr_cell_5_421:
    cmp rsi, rax
__sbr_cell_5_421_end:
__sbr_cell_5_422:
    jne ff_ps_read_data.L6d0
__sbr_cell_5_422_end:
__sbr_cell_5_423:
    cmp esi, r10d
__sbr_cell_5_423_end:
__sbr_cell_5_424:
    je ff_ps_read_data.L715
__sbr_cell_5_424_end:
ff_ps_read_data.L6f5:
__sbr_cell_5_425:
    lea rax, [r10+1]
__sbr_cell_5_425_end:
__sbr_cell_5_426:
    mov esi, edx
__sbr_cell_5_426_end:
__sbr_cell_5_427:
    shl esi, 5
__sbr_cell_5_427_end:
__sbr_cell_5_428:
    .nops 1
__sbr_cell_5_428_end:
ff_ps_read_data.L700:
__sbr_cell_5_429:
    mov edi, esi
__sbr_cell_5_429_end:
__sbr_cell_5_430:
    shr edi, cl
__sbr_cell_5_430_end:
__sbr_cell_5_431:
    dec edi
__sbr_cell_5_431_end:
__sbr_cell_5_432:
    mov DWORD PTR [rbx+rdx*4+52], edi
__sbr_cell_5_432_end:
__sbr_cell_5_433:
    inc rdx
__sbr_cell_5_433_end:
__sbr_cell_5_434:
    add esi, 32
__sbr_cell_5_434_end:
__sbr_cell_5_435:
    cmp rax, rdx
__sbr_cell_5_435_end:
__sbr_cell_5_436:
    jne ff_ps_read_data.L700
__sbr_cell_5_436_end:
ff_ps_read_data.L715:
__sbr_cell_5_437:
    mov eax, DWORD PTR [rbx+4]
__sbr_cell_5_437_end:
__sbr_cell_5_438:
    mov DWORD PTR [rbp-108], eax
__sbr_cell_5_438_end:
ff_ps_read_data.L71b:
__sbr_cell_5_439:
    test eax, eax
__sbr_cell_5_439_end:
__sbr_cell_5_440:
    mov QWORD PTR [rbp-56], rbx
__sbr_cell_5_440_end:
__sbr_cell_5_441:
    mov QWORD PTR [rbp-96], r10
__sbr_cell_5_441_end:
__sbr_cell_5_442:
    je ff_ps_read_data.La1e
__sbr_cell_5_442_end:
__sbr_cell_5_443:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_5_443_end:
__sbr_cell_5_444:
    test al, al
__sbr_cell_5_444_end:
__sbr_cell_5_445:
    jle ff_ps_read_data.La4c
__sbr_cell_5_445_end:
ff_ps_read_data.L737:
__sbr_cell_5_446:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_5_446_end:
__sbr_cell_5_447:
    lea r14, [rbx+76]
__sbr_cell_5_447_end:
__sbr_cell_5_448:
    mov QWORD PTR [rbp-80], rcx
__sbr_cell_5_448_end:
__sbr_cell_5_449:
    lea r9d, [rcx*8+7]
__sbr_cell_5_449_end:
ff_ps_read_data.L74a:
__sbr_cell_5_450:
    mov eax, eax
__sbr_cell_5_450_end:
__sbr_cell_5_451:
    mov QWORD PTR [rbp-120], rax
__sbr_cell_5_451_end:
__sbr_cell_5_452:
    xor ebx, ebx
__sbr_cell_5_452_end:
__sbr_cell_5_453:
    mov QWORD PTR [rbp-128], r14
__sbr_cell_5_453_end:
__sbr_cell_5_454:
    jmp ff_ps_read_data.L775
__sbr_cell_5_454_end:
__sbr_cell_5_455:
    .nops 1
__sbr_cell_5_455_end:
ff_ps_read_data.L760:
__sbr_cell_5_456:
    inc rbx
__sbr_cell_5_456_end:
__sbr_cell_5_457:
    add r14, 34
__sbr_cell_5_457_end:
__sbr_cell_5_458:
    cmp rbx, QWORD PTR [rbp-120]
__sbr_cell_5_458_end:
__sbr_cell_5_459:
    mov r10, QWORD PTR [rbp-96]
__sbr_cell_5_459_end:
__sbr_cell_5_460:
    je ff_ps_read_data.La4c
__sbr_cell_5_460_end:
ff_ps_read_data.L775:
__sbr_cell_5_461:
    mov eax, r8d
__sbr_cell_5_461_end:
__sbr_cell_5_462:
    shr eax, 3
__sbr_cell_5_462_end:
__sbr_cell_5_463:
    xor edx, edx
__sbr_cell_5_463_end:
__sbr_cell_5_464:
    cmp r8d, r12d
__sbr_cell_5_464_end:
__sbr_cell_5_465:
    setl sil
__sbr_cell_5_465_end:
__sbr_cell_5_466:
    movzx eax, BYTE PTR [r13+rax*1+0]
__sbr_cell_5_466_end:
__sbr_cell_5_467:
    mov ecx, r8d
__sbr_cell_5_467_end:
__sbr_cell_5_468:
    and cl, 7
__sbr_cell_5_468_end:
__sbr_cell_5_469:
    shl eax, cl
__sbr_cell_5_469_end:
__sbr_cell_5_470:
    shr eax, 7
__sbr_cell_5_470_end:
__sbr_cell_5_471:
    and eax, 1
__sbr_cell_5_471_end:
ff_ps_read_data.L798:
__sbr_cell_5_472:
    mov rcx, QWORD PTR [rbp-80]
__sbr_cell_5_472_end:
__sbr_cell_5_473:
    lea ecx, [rcx+rax*2+0]
__sbr_cell_5_473_end:
__sbr_cell_5_474:
    cmp ecx, 4
__sbr_cell_5_474_end:
__sbr_cell_5_475:
    jae ff_ps_read_data.L179a
__sbr_cell_5_475_end:
ff_ps_read_data.L7a8:
__sbr_cell_5_476:
    mov dl, sil
__sbr_cell_5_476_end:
__sbr_cell_5_477:
    add r8d, edx
__sbr_cell_5_477_end:
__sbr_cell_5_478:
    mov rdx, QWORD PTR [rbp-56]
__sbr_cell_5_478_end:
__sbr_cell_5_479:
    mov r11d, DWORD PTR [rdx+12]
__sbr_cell_5_479_end:
__sbr_cell_5_480:
    mov ecx, ecx
__sbr_cell_5_480_end:
__sbr_cell_5_481:
    lea rdx, [rip+huff_iid]
__sbr_cell_5_481_end:
__sbr_cell_5_482:
    mov ecx, DWORD PTR [rdx+rcx*4+0]
__sbr_cell_5_482_end:
__sbr_cell_5_483:
    lea rdx, [rip+vlc_ps]
__sbr_cell_5_483_end:
__sbr_cell_5_484:
    mov r15, QWORD PTR [rdx+rcx*8+0]
__sbr_cell_5_484_end:
__sbr_cell_5_485:
    test eax, eax
__sbr_cell_5_485_end:
__sbr_cell_5_486:
    jne ff_ps_read_data.L8d0
__sbr_cell_5_486_end:
ff_ps_read_data.L7d5:
__sbr_cell_5_487:
    test r11d, r11d
__sbr_cell_5_487_end:
__sbr_cell_5_488:
    jle ff_ps_read_data.L760
__sbr_cell_5_488_end:
__sbr_cell_5_489:
    xor edi, edi
__sbr_cell_5_489_end:
__sbr_cell_5_490:
    xor r10d, r10d
__sbr_cell_5_490_end:
__sbr_cell_5_491:
    .nops 1
__sbr_cell_5_491_end:
ff_ps_read_data.L7e0:
__sbr_cell_5_492:
    mov eax, r8d
__sbr_cell_5_492_end:
__sbr_cell_5_493:
    shr eax, 3
__sbr_cell_5_493_end:
__sbr_cell_5_494:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_494_end:
__sbr_cell_5_495:
    bswap eax
__sbr_cell_5_495_end:
__sbr_cell_5_496:
    mov ecx, r8d
__sbr_cell_5_496_end:
__sbr_cell_5_497:
    and cl, 7
__sbr_cell_5_497_end:
__sbr_cell_5_498:
    shl eax, cl
__sbr_cell_5_498_end:
__sbr_cell_5_499:
    shr eax, 23
__sbr_cell_5_499_end:
ff_ps_read_data.L7f8:
__sbr_cell_5_500:
    mov eax, eax
__sbr_cell_5_500_end:
__sbr_cell_5_501:
    movsx esi, WORD PTR [r15+rax*4+0]
__sbr_cell_5_501_end:
__sbr_cell_5_502:
    movsx eax, WORD PTR [r15+rax*4+2]
__sbr_cell_5_502_end:
__sbr_cell_5_503:
    test eax, eax
__sbr_cell_5_503_end:
__sbr_cell_5_504:
    jns ff_ps_read_data.L880
__sbr_cell_5_504_end:
ff_ps_read_data.L809:
__sbr_cell_5_505:
    add r8d, 9
__sbr_cell_5_505_end:
__sbr_cell_5_506:
    cmp r12d, r8d
__sbr_cell_5_506_end:
__sbr_cell_5_507:
    cmovb r8d, r12d
__sbr_cell_5_507_end:
__sbr_cell_5_508:
    mov ecx, r8d
__sbr_cell_5_508_end:
__sbr_cell_5_509:
    shr ecx, 3
__sbr_cell_5_509_end:
__sbr_cell_5_510:
    mov edx, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_510_end:
__sbr_cell_5_511:
    bswap edx
__sbr_cell_5_511_end:
__sbr_cell_5_512:
    mov ecx, r8d
__sbr_cell_5_512_end:
__sbr_cell_5_513:
    and cl, 7
__sbr_cell_5_513_end:
__sbr_cell_5_514:
    shl edx, cl
__sbr_cell_5_514_end:
ff_ps_read_data.L829:
__sbr_cell_5_515:
    mov ecx, eax
__sbr_cell_5_515_end:
__sbr_cell_5_516:
    shr edx, cl
__sbr_cell_5_516_end:
__sbr_cell_5_517:
    add edx, esi
__sbr_cell_5_517_end:
__sbr_cell_5_518:
    movsx esi, WORD PTR [r15+rdx*4+0]
__sbr_cell_5_518_end:
__sbr_cell_5_519:
    movsx edx, WORD PTR [r15+rdx*4+2]
__sbr_cell_5_519_end:
__sbr_cell_5_520:
    test edx, edx
__sbr_cell_5_520_end:
__sbr_cell_5_521:
    js ff_ps_read_data.L842
__sbr_cell_5_521_end:
__sbr_cell_5_522:
    mov eax, edx
__sbr_cell_5_522_end:
__sbr_cell_5_523:
    jmp ff_ps_read_data.L880
__sbr_cell_5_523_end:
ff_ps_read_data.L842:
__sbr_cell_5_524:
    sub r8d, eax
__sbr_cell_5_524_end:
__sbr_cell_5_525:
    cmp r12d, r8d
__sbr_cell_5_525_end:
__sbr_cell_5_526:
    cmovb r8d, r12d
__sbr_cell_5_526_end:
__sbr_cell_5_527:
    mov eax, r8d
__sbr_cell_5_527_end:
__sbr_cell_5_528:
    shr eax, 3
__sbr_cell_5_528_end:
__sbr_cell_5_529:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_529_end:
__sbr_cell_5_530:
    bswap eax
__sbr_cell_5_530_end:
__sbr_cell_5_531:
    mov ecx, r8d
__sbr_cell_5_531_end:
__sbr_cell_5_532:
    and cl, 7
__sbr_cell_5_532_end:
__sbr_cell_5_533:
    shl eax, cl
__sbr_cell_5_533_end:
ff_ps_read_data.L861:
__sbr_cell_5_534:
    mov ecx, edx
__sbr_cell_5_534_end:
__sbr_cell_5_535:
    shr eax, cl
__sbr_cell_5_535_end:
__sbr_cell_5_536:
    add eax, esi
__sbr_cell_5_536_end:
__sbr_cell_5_537:
    movzx esi, WORD PTR [r15+rax*4+0]
__sbr_cell_5_537_end:
__sbr_cell_5_538:
    movsx eax, WORD PTR [r15+rax*4+2]
__sbr_cell_5_538_end:
__sbr_cell_5_539:
    .nops 1
__sbr_cell_5_539_end:
ff_ps_read_data.L880:
__sbr_cell_5_540:
    add r8d, eax
__sbr_cell_5_540_end:
__sbr_cell_5_541:
    cmp r12d, r8d
__sbr_cell_5_541_end:
__sbr_cell_5_542:
    cmovb r8d, r12d
__sbr_cell_5_542_end:
__sbr_cell_5_543:
    cmp r10, 34
__sbr_cell_5_543_end:
__sbr_cell_5_544:
    je ff_ps_read_data.L1777
__sbr_cell_5_544_end:
__sbr_cell_5_545:
    add edi, esi
__sbr_cell_5_545_end:
__sbr_cell_5_546:
    mov BYTE PTR [r14+r10*1+0], dil
__sbr_cell_5_546_end:
__sbr_cell_5_547:
    cmp rbx, 5
__sbr_cell_5_547_end:
__sbr_cell_5_548:
    jae ff_ps_read_data.L177c
__sbr_cell_5_548_end:
ff_ps_read_data.L8a4:
__sbr_cell_5_549:
    mov eax, edi
__sbr_cell_5_549_end:
__sbr_cell_5_550:
    sar al, 7
__sbr_cell_5_550_end:
__sbr_cell_5_551:
    mov ecx, edi
__sbr_cell_5_551_end:
__sbr_cell_5_552:
    xor cl, al
__sbr_cell_5_552_end:
__sbr_cell_5_553:
    sub cl, al
__sbr_cell_5_553_end:
__sbr_cell_5_554:
    movzx eax, cl
__sbr_cell_5_554_end:
__sbr_cell_5_555:
    cmp r9d, eax
__sbr_cell_5_555_end:
__sbr_cell_5_556:
    jl ff_ps_read_data.Lc7a
__sbr_cell_5_556_end:
ff_ps_read_data.L8bb:
__sbr_cell_5_557:
    inc r10
__sbr_cell_5_557_end:
__sbr_cell_5_558:
    cmp r11, r10
__sbr_cell_5_558_end:
__sbr_cell_5_559:
    jne ff_ps_read_data.L7e0
__sbr_cell_5_559_end:
__sbr_cell_5_560:
    jmp ff_ps_read_data.L760
__sbr_cell_5_560_end:
__sbr_cell_5_561:
    .nops 1
__sbr_cell_5_561_end:
ff_ps_read_data.L8d0:
__sbr_cell_5_562:
    test r11d, r11d
__sbr_cell_5_562_end:
__sbr_cell_5_563:
    jle ff_ps_read_data.L760
__sbr_cell_5_563_end:
__sbr_cell_5_564:
    test rbx, rbx
__sbr_cell_5_564_end:
__sbr_cell_5_565:
    mov eax, ebx
__sbr_cell_5_565_end:
__sbr_cell_5_566:
    cmove eax, DWORD PTR [rbp-104]
__sbr_cell_5_566_end:
__sbr_cell_5_567:
    cmp eax, 2
__sbr_cell_5_567_end:
__sbr_cell_5_568:
    mov ecx, 1
__sbr_cell_5_568_end:
__sbr_cell_5_569:
    cmovl eax, ecx
__sbr_cell_5_569_end:
ff_ps_read_data.L8ed:
__sbr_cell_5_570:
    mov rcx, rax
__sbr_cell_5_570_end:
__sbr_cell_5_571:
    shl rcx, 5
__sbr_cell_5_571_end:
__sbr_cell_5_572:
    lea rdx, [rcx+rax*2+0]
__sbr_cell_5_572_end:
__sbr_cell_5_573:
    add rdx, QWORD PTR [rbp-128]
__sbr_cell_5_573_end:
__sbr_cell_5_574:
    xor r10d, r10d
__sbr_cell_5_574_end:
__sbr_cell_5_575:
    mov QWORD PTR [rbp-88], r14
__sbr_cell_5_575_end:
__sbr_cell_5_576:
    .nops 1
__sbr_cell_5_576_end:
ff_ps_read_data.L910:
__sbr_cell_5_577:
    cmp r10, 34
__sbr_cell_5_577_end:
__sbr_cell_5_578:
    je ff_ps_read_data.L176d
__sbr_cell_5_578_end:
__sbr_cell_5_579:
    movzx esi, BYTE PTR [rdx+r10*1-34]
__sbr_cell_5_579_end:
__sbr_cell_5_580:
    mov eax, r8d
__sbr_cell_5_580_end:
__sbr_cell_5_581:
    shr eax, 3
__sbr_cell_5_581_end:
__sbr_cell_5_582:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_582_end:
__sbr_cell_5_583:
    bswap eax
__sbr_cell_5_583_end:
__sbr_cell_5_584:
    mov ecx, r8d
__sbr_cell_5_584_end:
__sbr_cell_5_585:
    and cl, 7
__sbr_cell_5_585_end:
__sbr_cell_5_586:
    shl eax, cl
__sbr_cell_5_586_end:
__sbr_cell_5_587:
    shr eax, 23
__sbr_cell_5_587_end:
ff_ps_read_data.L938:
__sbr_cell_5_588:
    mov eax, eax
__sbr_cell_5_588_end:
__sbr_cell_5_589:
    movzx ecx, WORD PTR [r15+rax*4+0]
__sbr_cell_5_589_end:
__sbr_cell_5_590:
    movsx eax, WORD PTR [r15+rax*4+2]
__sbr_cell_5_590_end:
__sbr_cell_5_591:
    test eax, eax
__sbr_cell_5_591_end:
__sbr_cell_5_592:
    jns ff_ps_read_data.L9da
__sbr_cell_5_592_end:
ff_ps_read_data.L94d:
__sbr_cell_5_593:
    mov r14, rdx
__sbr_cell_5_593_end:
__sbr_cell_5_594:
    mov rdi, r11
__sbr_cell_5_594_end:
__sbr_cell_5_595:
    mov r11d, r9d
__sbr_cell_5_595_end:
__sbr_cell_5_596:
    movsx edx, cx
__sbr_cell_5_596_end:
__sbr_cell_5_597:
    add r8d, 9
__sbr_cell_5_597_end:
__sbr_cell_5_598:
    cmp r12d, r8d
__sbr_cell_5_598_end:
__sbr_cell_5_599:
    cmovb r8d, r12d
__sbr_cell_5_599_end:
__sbr_cell_5_600:
    mov ecx, r8d
__sbr_cell_5_600_end:
__sbr_cell_5_601:
    shr ecx, 3
__sbr_cell_5_601_end:
__sbr_cell_5_602:
    mov r9d, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_602_end:
ff_ps_read_data.L96f:
__sbr_cell_5_603:
    bswap r9d
__sbr_cell_5_603_end:
__sbr_cell_5_604:
    mov ecx, r8d
__sbr_cell_5_604_end:
__sbr_cell_5_605:
    and cl, 7
__sbr_cell_5_605_end:
__sbr_cell_5_606:
    shl r9d, cl
__sbr_cell_5_606_end:
__sbr_cell_5_607:
    mov ecx, eax
__sbr_cell_5_607_end:
__sbr_cell_5_608:
    shr r9d, cl
__sbr_cell_5_608_end:
__sbr_cell_5_609:
    add r9d, edx
__sbr_cell_5_609_end:
ff_ps_read_data.L983:
__sbr_cell_5_610:
    movzx ecx, WORD PTR [r15+r9*4+0]
__sbr_cell_5_610_end:
__sbr_cell_5_611:
    movsx edx, WORD PTR [r15+r9*4+2]
__sbr_cell_5_611_end:
__sbr_cell_5_612:
    test edx, edx
__sbr_cell_5_612_end:
__sbr_cell_5_613:
    js ff_ps_read_data.L996
__sbr_cell_5_613_end:
__sbr_cell_5_614:
    mov eax, edx
__sbr_cell_5_614_end:
__sbr_cell_5_615:
    jmp ff_ps_read_data.L9cd
__sbr_cell_5_615_end:
ff_ps_read_data.L996:
__sbr_cell_5_616:
    sub r8d, eax
__sbr_cell_5_616_end:
__sbr_cell_5_617:
    cmp r12d, r8d
__sbr_cell_5_617_end:
__sbr_cell_5_618:
    cmovb r8d, r12d
__sbr_cell_5_618_end:
__sbr_cell_5_619:
    movsx eax, cx
__sbr_cell_5_619_end:
__sbr_cell_5_620:
    mov ecx, r8d
__sbr_cell_5_620_end:
__sbr_cell_5_621:
    shr ecx, 3
__sbr_cell_5_621_end:
__sbr_cell_5_622:
    mov r9d, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_622_end:
__sbr_cell_5_623:
    bswap r9d
__sbr_cell_5_623_end:
ff_ps_read_data.L9b1:
__sbr_cell_5_624:
    mov ecx, r8d
__sbr_cell_5_624_end:
__sbr_cell_5_625:
    and cl, 7
__sbr_cell_5_625_end:
__sbr_cell_5_626:
    shl r9d, cl
__sbr_cell_5_626_end:
__sbr_cell_5_627:
    mov ecx, edx
__sbr_cell_5_627_end:
__sbr_cell_5_628:
    shr r9d, cl
__sbr_cell_5_628_end:
__sbr_cell_5_629:
    add r9d, eax
__sbr_cell_5_629_end:
__sbr_cell_5_630:
    movzx ecx, WORD PTR [r15+r9*4+0]
__sbr_cell_5_630_end:
__sbr_cell_5_631:
    movsx eax, WORD PTR [r15+r9*4+2]
__sbr_cell_5_631_end:
ff_ps_read_data.L9cd:
__sbr_cell_5_632:
    mov r9d, r11d
__sbr_cell_5_632_end:
__sbr_cell_5_633:
    mov r11, rdi
__sbr_cell_5_633_end:
__sbr_cell_5_634:
    mov rdx, r14
__sbr_cell_5_634_end:
__sbr_cell_5_635:
    mov r14, QWORD PTR [rbp-88]
__sbr_cell_5_635_end:
ff_ps_read_data.L9da:
__sbr_cell_5_636:
    add r8d, eax
__sbr_cell_5_636_end:
__sbr_cell_5_637:
    cmp r12d, r8d
__sbr_cell_5_637_end:
__sbr_cell_5_638:
    cmovb r8d, r12d
__sbr_cell_5_638_end:
__sbr_cell_5_639:
    add sil, cl
__sbr_cell_5_639_end:
__sbr_cell_5_640:
    mov BYTE PTR [r14+r10*1+0], sil
__sbr_cell_5_640_end:
__sbr_cell_5_641:
    cmp rbx, 5
__sbr_cell_5_641_end:
__sbr_cell_5_642:
    jae ff_ps_read_data.L1772
__sbr_cell_5_642_end:
ff_ps_read_data.L9f5:
__sbr_cell_5_643:
    mov eax, esi
__sbr_cell_5_643_end:
__sbr_cell_5_644:
    sar al, 7
__sbr_cell_5_644_end:
__sbr_cell_5_645:
    xor sil, al
__sbr_cell_5_645_end:
__sbr_cell_5_646:
    sub sil, al
__sbr_cell_5_646_end:
__sbr_cell_5_647:
    movzx eax, sil
__sbr_cell_5_647_end:
__sbr_cell_5_648:
    cmp r9d, eax
__sbr_cell_5_648_end:
__sbr_cell_5_649:
    jl ff_ps_read_data.Lc7a
__sbr_cell_5_649_end:
__sbr_cell_5_650:
    inc r10
__sbr_cell_5_650_end:
__sbr_cell_5_651:
    cmp r11, r10
__sbr_cell_5_651_end:
__sbr_cell_5_652:
    jne ff_ps_read_data.L910
__sbr_cell_5_652_end:
__sbr_cell_5_653:
    jmp ff_ps_read_data.L760
__sbr_cell_5_653_end:
ff_ps_read_data.La1e:
__sbr_cell_5_654:
    vpxor xmm0, xmm0, xmm0
__sbr_cell_5_654_end:
__sbr_cell_5_655:
    vmovdqu YMMWORD PTR [rbx+214], ymm0
__sbr_cell_5_655_end:
__sbr_cell_5_656:
    vmovdqu YMMWORD PTR [rbx+204], ymm0
__sbr_cell_5_656_end:
ff_ps_read_data.La32:
__sbr_cell_5_657:
    vmovdqu YMMWORD PTR [rbx+172], ymm0
__sbr_cell_5_657_end:
__sbr_cell_5_658:
    vmovdqu YMMWORD PTR [rbx+140], ymm0
__sbr_cell_5_658_end:
ff_ps_read_data.La42:
__sbr_cell_5_659:
    vmovdqu YMMWORD PTR [rbx+108], ymm0
__sbr_cell_5_659_end:
__sbr_cell_5_660:
    vmovdqu YMMWORD PTR [rbx+76], ymm0
__sbr_cell_5_660_end:
ff_ps_read_data.La4c:
__sbr_cell_5_661:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_5_661_end:
__sbr_cell_5_662:
    mov ecx, DWORD PTR [rax+20]
__sbr_cell_5_662_end:
__sbr_cell_5_663:
    mov DWORD PTR [rbp-132], ecx
__sbr_cell_5_663_end:
__sbr_cell_5_664:
    test ecx, ecx
__sbr_cell_5_664_end:
__sbr_cell_5_665:
    je ff_ps_read_data.Lc86
__sbr_cell_5_665_end:
__sbr_cell_5_666:
    test r10b, r10b
__sbr_cell_5_666_end:
__sbr_cell_5_667:
    jle ff_ps_read_data.Lcba
__sbr_cell_5_667_end:
ff_ps_read_data.La6a:
__sbr_cell_5_668:
    lea rbx, [rax+246]
__sbr_cell_5_668_end:
__sbr_cell_5_669:
    mov esi, DWORD PTR [rax+28]
__sbr_cell_5_669_end:
__sbr_cell_5_670:
    mov eax, DWORD PTR [rbp-72]
__sbr_cell_5_670_end:
__sbr_cell_5_671:
    mov QWORD PTR [rbp-88], rax
__sbr_cell_5_671_end:
__sbr_cell_5_672:
    xor r9d, r9d
__sbr_cell_5_672_end:
__sbr_cell_5_673:
    mov QWORD PTR [rbp-80], rbx
__sbr_cell_5_673_end:
__sbr_cell_5_674:
    jmp ff_ps_read_data.Laa5
__sbr_cell_5_674_end:
__sbr_cell_5_675:
    .nops 1
__sbr_cell_5_675_end:
ff_ps_read_data.La90:
__sbr_cell_5_676:
    inc r9
__sbr_cell_5_676_end:
__sbr_cell_5_677:
    add rbx, 34
__sbr_cell_5_677_end:
__sbr_cell_5_678:
    cmp r9, QWORD PTR [rbp-88]
__sbr_cell_5_678_end:
__sbr_cell_5_679:
    mov r10, QWORD PTR [rbp-96]
__sbr_cell_5_679_end:
__sbr_cell_5_680:
    je ff_ps_read_data.Lcba
__sbr_cell_5_680_end:
ff_ps_read_data.Laa5:
__sbr_cell_5_681:
    mov ecx, r8d
__sbr_cell_5_681_end:
__sbr_cell_5_682:
    mov eax, r8d
__sbr_cell_5_682_end:
__sbr_cell_5_683:
    shr eax, 3
__sbr_cell_5_683_end:
__sbr_cell_5_684:
    xor r8d, r8d
__sbr_cell_5_684_end:
__sbr_cell_5_685:
    cmp ecx, r12d
__sbr_cell_5_685_end:
__sbr_cell_5_686:
    setl r8b
__sbr_cell_5_686_end:
__sbr_cell_5_687:
    add r8d, ecx
__sbr_cell_5_687_end:
__sbr_cell_5_688:
    and cl, 7
__sbr_cell_5_688_end:
__sbr_cell_5_689:
    mov edx, 128
__sbr_cell_5_689_end:
__sbr_cell_5_690:
    shr edx, cl
__sbr_cell_5_690_end:
ff_ps_read_data.Lac5:
__sbr_cell_5_691:
    movzx eax, BYTE PTR [r13+rax*1+0]
__sbr_cell_5_691_end:
__sbr_cell_5_692:
    xor ecx, ecx
__sbr_cell_5_692_end:
__sbr_cell_5_693:
    test edx, eax
__sbr_cell_5_693_end:
__sbr_cell_5_694:
    sete cl
__sbr_cell_5_694_end:
__sbr_cell_5_695:
    xor ecx, 5
__sbr_cell_5_695_end:
__sbr_cell_5_696:
    lea rdi, [rip+vlc_ps]
__sbr_cell_5_696_end:
__sbr_cell_5_697:
    mov r14, QWORD PTR [rdi+rcx*8+0]
__sbr_cell_5_697_end:
__sbr_cell_5_698:
    test edx, eax
__sbr_cell_5_698_end:
__sbr_cell_5_699:
    je ff_ps_read_data.Lbc3
__sbr_cell_5_699_end:
__sbr_cell_5_700:
    test esi, esi
__sbr_cell_5_700_end:
__sbr_cell_5_701:
    jle ff_ps_read_data.La90
__sbr_cell_5_701_end:
ff_ps_read_data.Laec:
__sbr_cell_5_702:
    test r9, r9
__sbr_cell_5_702_end:
__sbr_cell_5_703:
    mov eax, r9d
__sbr_cell_5_703_end:
__sbr_cell_5_704:
    cmove eax, DWORD PTR [rbp-104]
__sbr_cell_5_704_end:
__sbr_cell_5_705:
    cmp eax, 2
__sbr_cell_5_705_end:
__sbr_cell_5_706:
    mov ecx, 1
__sbr_cell_5_706_end:
__sbr_cell_5_707:
    cmovl eax, ecx
__sbr_cell_5_707_end:
ff_ps_read_data.Lb01:
__sbr_cell_5_708:
    mov rcx, rax
__sbr_cell_5_708_end:
__sbr_cell_5_709:
    shl rcx, 5
__sbr_cell_5_709_end:
__sbr_cell_5_710:
    lea r15, [rcx+rax*2+0]
__sbr_cell_5_710_end:
__sbr_cell_5_711:
    add r15, QWORD PTR [rbp-80]
__sbr_cell_5_711_end:
__sbr_cell_5_712:
    xor r11d, r11d
__sbr_cell_5_712_end:
__sbr_cell_5_713:
    .nops 1
__sbr_cell_5_713_end:
ff_ps_read_data.Lb20:
__sbr_cell_5_714:
    cmp r11, 34
__sbr_cell_5_714_end:
__sbr_cell_5_715:
    je ff_ps_read_data.L1781
__sbr_cell_5_715_end:
__sbr_cell_5_716:
    movzx edx, BYTE PTR [r15+r11*1-34]
__sbr_cell_5_716_end:
__sbr_cell_5_717:
    mov eax, r8d
__sbr_cell_5_717_end:
__sbr_cell_5_718:
    shr eax, 3
__sbr_cell_5_718_end:
__sbr_cell_5_719:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_719_end:
__sbr_cell_5_720:
    bswap eax
__sbr_cell_5_720_end:
__sbr_cell_5_721:
    mov ecx, r8d
__sbr_cell_5_721_end:
__sbr_cell_5_722:
    and cl, 7
__sbr_cell_5_722_end:
__sbr_cell_5_723:
    shl eax, cl
__sbr_cell_5_723_end:
__sbr_cell_5_724:
    shr eax, 23
__sbr_cell_5_724_end:
ff_ps_read_data.Lb48:
__sbr_cell_5_725:
    mov eax, eax
__sbr_cell_5_725_end:
__sbr_cell_5_726:
    movzx ecx, WORD PTR [r14+rax*4+0]
__sbr_cell_5_726_end:
__sbr_cell_5_727:
    movsx eax, WORD PTR [r14+rax*4+2]
__sbr_cell_5_727_end:
__sbr_cell_5_728:
    test eax, eax
__sbr_cell_5_728_end:
__sbr_cell_5_729:
    jns ff_ps_read_data.Lb8f
__sbr_cell_5_729_end:
ff_ps_read_data.Lb59:
__sbr_cell_5_730:
    add r8d, 9
__sbr_cell_5_730_end:
__sbr_cell_5_731:
    cmp r12d, r8d
__sbr_cell_5_731_end:
__sbr_cell_5_732:
    cmovb r8d, r12d
__sbr_cell_5_732_end:
__sbr_cell_5_733:
    movsx r10d, cx
__sbr_cell_5_733_end:
__sbr_cell_5_734:
    mov ecx, r8d
__sbr_cell_5_734_end:
__sbr_cell_5_735:
    shr ecx, 3
__sbr_cell_5_735_end:
__sbr_cell_5_736:
    mov edi, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_736_end:
__sbr_cell_5_737:
    bswap edi
__sbr_cell_5_737_end:
ff_ps_read_data.Lb75:
__sbr_cell_5_738:
    mov ecx, r8d
__sbr_cell_5_738_end:
__sbr_cell_5_739:
    and cl, 7
__sbr_cell_5_739_end:
__sbr_cell_5_740:
    shl edi, cl
__sbr_cell_5_740_end:
__sbr_cell_5_741:
    mov ecx, eax
__sbr_cell_5_741_end:
__sbr_cell_5_742:
    shr edi, cl
__sbr_cell_5_742_end:
__sbr_cell_5_743:
    add edi, r10d
__sbr_cell_5_743_end:
__sbr_cell_5_744:
    movzx ecx, WORD PTR [r14+rdi*4+0]
__sbr_cell_5_744_end:
__sbr_cell_5_745:
    movsx eax, WORD PTR [r14+rdi*4+2]
__sbr_cell_5_745_end:
ff_ps_read_data.Lb8f:
__sbr_cell_5_746:
    add r8d, eax
__sbr_cell_5_746_end:
__sbr_cell_5_747:
    cmp r12d, r8d
__sbr_cell_5_747_end:
__sbr_cell_5_748:
    cmovb r8d, r12d
__sbr_cell_5_748_end:
__sbr_cell_5_749:
    add dl, cl
__sbr_cell_5_749_end:
__sbr_cell_5_750:
    mov BYTE PTR [rbx+r11*1+0], dl
__sbr_cell_5_750_end:
__sbr_cell_5_751:
    cmp r9, 5
__sbr_cell_5_751_end:
__sbr_cell_5_752:
    jae ff_ps_read_data.L1786
__sbr_cell_5_752_end:
ff_ps_read_data.Lba9:
__sbr_cell_5_753:
    cmp dl, 8
__sbr_cell_5_753_end:
__sbr_cell_5_754:
    jae ff_ps_read_data.L10cf
__sbr_cell_5_754_end:
__sbr_cell_5_755:
    inc r11
__sbr_cell_5_755_end:
__sbr_cell_5_756:
    cmp rsi, r11
__sbr_cell_5_756_end:
__sbr_cell_5_757:
    jne ff_ps_read_data.Lb20
__sbr_cell_5_757_end:
__sbr_cell_5_758:
    jmp ff_ps_read_data.La90
__sbr_cell_5_758_end:
ff_ps_read_data.Lbc3:
__sbr_cell_5_759:
    test esi, esi
__sbr_cell_5_759_end:
__sbr_cell_5_760:
    jle ff_ps_read_data.La90
__sbr_cell_5_760_end:
__sbr_cell_5_761:
    xor r15d, r15d
__sbr_cell_5_761_end:
__sbr_cell_5_762:
    xor r11d, r11d
__sbr_cell_5_762_end:
__sbr_cell_5_763:
    .nops 1
__sbr_cell_5_763_end:
ff_ps_read_data.Lbe0:
__sbr_cell_5_764:
    mov eax, r8d
__sbr_cell_5_764_end:
__sbr_cell_5_765:
    shr eax, 3
__sbr_cell_5_765_end:
__sbr_cell_5_766:
    mov eax, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_766_end:
__sbr_cell_5_767:
    bswap eax
__sbr_cell_5_767_end:
__sbr_cell_5_768:
    mov ecx, r8d
__sbr_cell_5_768_end:
__sbr_cell_5_769:
    and cl, 7
__sbr_cell_5_769_end:
__sbr_cell_5_770:
    shl eax, cl
__sbr_cell_5_770_end:
__sbr_cell_5_771:
    shr eax, 23
__sbr_cell_5_771_end:
ff_ps_read_data.Lbf8:
__sbr_cell_5_772:
    mov eax, eax
__sbr_cell_5_772_end:
__sbr_cell_5_773:
    movsx edx, WORD PTR [r14+rax*4+0]
__sbr_cell_5_773_end:
__sbr_cell_5_774:
    movsx eax, WORD PTR [r14+rax*4+2]
__sbr_cell_5_774_end:
__sbr_cell_5_775:
    test eax, eax
__sbr_cell_5_775_end:
__sbr_cell_5_776:
    jns ff_ps_read_data.Lc3a
__sbr_cell_5_776_end:
ff_ps_read_data.Lc09:
__sbr_cell_5_777:
    add r8d, 9
__sbr_cell_5_777_end:
__sbr_cell_5_778:
    cmp r12d, r8d
__sbr_cell_5_778_end:
__sbr_cell_5_779:
    cmovb r8d, r12d
__sbr_cell_5_779_end:
__sbr_cell_5_780:
    mov ecx, r8d
__sbr_cell_5_780_end:
__sbr_cell_5_781:
    shr ecx, 3
__sbr_cell_5_781_end:
__sbr_cell_5_782:
    mov edi, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_782_end:
__sbr_cell_5_783:
    bswap edi
__sbr_cell_5_783_end:
__sbr_cell_5_784:
    mov ecx, r8d
__sbr_cell_5_784_end:
__sbr_cell_5_785:
    and cl, 7
__sbr_cell_5_785_end:
__sbr_cell_5_786:
    shl edi, cl
__sbr_cell_5_786_end:
ff_ps_read_data.Lc29:
__sbr_cell_5_787:
    mov ecx, eax
__sbr_cell_5_787_end:
__sbr_cell_5_788:
    shr edi, cl
__sbr_cell_5_788_end:
__sbr_cell_5_789:
    add edi, edx
__sbr_cell_5_789_end:
__sbr_cell_5_790:
    movzx edx, WORD PTR [r14+rdi*4+0]
__sbr_cell_5_790_end:
__sbr_cell_5_791:
    movsx eax, WORD PTR [r14+rdi*4+2]
__sbr_cell_5_791_end:
ff_ps_read_data.Lc3a:
__sbr_cell_5_792:
    add r8d, eax
__sbr_cell_5_792_end:
__sbr_cell_5_793:
    cmp r12d, r8d
__sbr_cell_5_793_end:
__sbr_cell_5_794:
    cmovb r8d, r12d
__sbr_cell_5_794_end:
__sbr_cell_5_795:
    cmp r11, 34
__sbr_cell_5_795_end:
__sbr_cell_5_796:
    je ff_ps_read_data.L1790
__sbr_cell_5_796_end:
__sbr_cell_5_797:
    add r15d, edx
__sbr_cell_5_797_end:
__sbr_cell_5_798:
    mov BYTE PTR [rbx+r11*1+0], r15b
__sbr_cell_5_798_end:
__sbr_cell_5_799:
    cmp r9, 5
__sbr_cell_5_799_end:
__sbr_cell_5_800:
    jae ff_ps_read_data.L178b
__sbr_cell_5_800_end:
ff_ps_read_data.Lc5f:
__sbr_cell_5_801:
    cmp r15b, 8
__sbr_cell_5_801_end:
__sbr_cell_5_802:
    jae ff_ps_read_data.L10cf
__sbr_cell_5_802_end:
__sbr_cell_5_803:
    inc r11
__sbr_cell_5_803_end:
__sbr_cell_5_804:
    cmp rsi, r11
__sbr_cell_5_804_end:
__sbr_cell_5_805:
    jne ff_ps_read_data.Lbe0
__sbr_cell_5_805_end:
__sbr_cell_5_806:
    jmp ff_ps_read_data.La90
__sbr_cell_5_806_end:
ff_ps_read_data.Lc7a:
__sbr_cell_5_807:
    lea rdx, [rip+L_str_7]
__sbr_cell_5_807_end:
__sbr_cell_5_808:
    jmp ff_ps_read_data.L10d6
__sbr_cell_5_808_end:
ff_ps_read_data.Lc86:
__sbr_cell_5_809:
    vpxor xmm0, xmm0, xmm0
__sbr_cell_5_809_end:
__sbr_cell_5_810:
    vmovdqu YMMWORD PTR [rax+384], ymm0
__sbr_cell_5_810_end:
__sbr_cell_5_811:
    vmovdqu YMMWORD PTR [rax+374], ymm0
__sbr_cell_5_811_end:
ff_ps_read_data.Lc9a:
__sbr_cell_5_812:
    vmovdqu YMMWORD PTR [rax+342], ymm0
__sbr_cell_5_812_end:
__sbr_cell_5_813:
    vmovdqu YMMWORD PTR [rax+310], ymm0
__sbr_cell_5_813_end:
ff_ps_read_data.Lcaa:
__sbr_cell_5_814:
    vmovdqu YMMWORD PTR [rax+278], ymm0
__sbr_cell_5_814_end:
__sbr_cell_5_815:
    vmovdqu YMMWORD PTR [rax+246], ymm0
__sbr_cell_5_815_end:
ff_ps_read_data.Lcba:
__sbr_cell_5_816:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_5_816_end:
__sbr_cell_5_817:
    cmp DWORD PTR [rbx+32], 0
__sbr_cell_5_817_end:
__sbr_cell_5_818:
    je ff_ps_read_data.L1063
__sbr_cell_5_818_end:
ff_ps_read_data.Lcc8:
__sbr_cell_5_819:
    mov eax, r8d
__sbr_cell_5_819_end:
__sbr_cell_5_820:
    shr eax, 3
__sbr_cell_5_820_end:
__sbr_cell_5_821:
    mov edx, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_821_end:
__sbr_cell_5_822:
    bswap edx
__sbr_cell_5_822_end:
__sbr_cell_5_823:
    mov ecx, r8d
__sbr_cell_5_823_end:
__sbr_cell_5_824:
    and cl, 7
__sbr_cell_5_824_end:
__sbr_cell_5_825:
    shl edx, cl
__sbr_cell_5_825_end:
__sbr_cell_5_826:
    shr edx, 28
__sbr_cell_5_826_end:
ff_ps_read_data.Lce0:
__sbr_cell_5_827:
    add r8d, 4
__sbr_cell_5_827_end:
__sbr_cell_5_828:
    cmp r12d, r8d
__sbr_cell_5_828_end:
__sbr_cell_5_829:
    cmovb r8d, r12d
__sbr_cell_5_829_end:
__sbr_cell_5_830:
    cmp edx, 15
__sbr_cell_5_830_end:
__sbr_cell_5_831:
    jne ff_ps_read_data.Ld16
__sbr_cell_5_831_end:
ff_ps_read_data.Lcf0:
__sbr_cell_5_832:
    mov eax, r8d
__sbr_cell_5_832_end:
__sbr_cell_5_833:
    shr eax, 3
__sbr_cell_5_833_end:
__sbr_cell_5_834:
    mov edx, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_834_end:
__sbr_cell_5_835:
    bswap edx
__sbr_cell_5_835_end:
__sbr_cell_5_836:
    mov ecx, r8d
__sbr_cell_5_836_end:
__sbr_cell_5_837:
    and cl, 7
__sbr_cell_5_837_end:
__sbr_cell_5_838:
    shl edx, cl
__sbr_cell_5_838_end:
__sbr_cell_5_839:
    shr edx, 24
__sbr_cell_5_839_end:
ff_ps_read_data.Ld08:
__sbr_cell_5_840:
    add r8d, 8
__sbr_cell_5_840_end:
__sbr_cell_5_841:
    cmp r12d, r8d
__sbr_cell_5_841_end:
__sbr_cell_5_842:
    cmovb r8d, r12d
__sbr_cell_5_842_end:
__sbr_cell_5_843:
    add edx, 15
__sbr_cell_5_843_end:
ff_ps_read_data.Ld16:
__sbr_cell_5_844:
    lea eax, [rdx*8+0]
__sbr_cell_5_844_end:
__sbr_cell_5_845:
    test edx, edx
__sbr_cell_5_845_end:
__sbr_cell_5_846:
    jle ff_ps_read_data.L104e
__sbr_cell_5_846_end:
ff_ps_read_data.Ld25:
__sbr_cell_5_847:
    lea rcx, [rbx+416]
__sbr_cell_5_847_end:
__sbr_cell_5_848:
    mov QWORD PTR [rbp-80], rcx
__sbr_cell_5_848_end:
__sbr_cell_5_849:
    lea rcx, [rbx+586]
__sbr_cell_5_849_end:
__sbr_cell_5_850:
    mov QWORD PTR [rbp-120], rcx
__sbr_cell_5_850_end:
ff_ps_read_data.Ld3b:
__sbr_cell_5_851:
    mov ecx, DWORD PTR [rbp-72]
__sbr_cell_5_851_end:
__sbr_cell_5_852:
    mov QWORD PTR [rbp-88], rcx
__sbr_cell_5_852_end:
__sbr_cell_5_853:
    jmp ff_ps_read_data.Ld7b
__sbr_cell_5_853_end:
__sbr_cell_5_854:
    .nops 1
__sbr_cell_5_854_end:
ff_ps_read_data.Ld50:
__sbr_cell_5_855:
    inc edx
__sbr_cell_5_855_end:
__sbr_cell_5_856:
    cmp r12d, edx
__sbr_cell_5_856_end:
__sbr_cell_5_857:
    cmovb edx, r12d
__sbr_cell_5_857_end:
__sbr_cell_5_858:
    sub r8d, edx
__sbr_cell_5_858_end:
__sbr_cell_5_859:
    mov ecx, r8d
__sbr_cell_5_859_end:
__sbr_cell_5_860:
    add ecx, 4294967294
__sbr_cell_5_860_end:
__sbr_cell_5_861:
    mov r8d, edx
__sbr_cell_5_861_end:
__sbr_cell_5_862:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_5_862_end:
__sbr_cell_5_863:
    mov r10, QWORD PTR [rbp-96]
__sbr_cell_5_863_end:
__sbr_cell_5_864:
    mov eax, DWORD PTR [rbp-128]
__sbr_cell_5_864_end:
ff_ps_read_data.Ld70:
__sbr_cell_5_865:
    add eax, ecx
__sbr_cell_5_865_end:
__sbr_cell_5_866:
    cmp eax, 7
__sbr_cell_5_866_end:
__sbr_cell_5_867:
    jle ff_ps_read_data.L104e
__sbr_cell_5_867_end:
ff_ps_read_data.Ld7b:
__sbr_cell_5_868:
    mov ecx, r8d
__sbr_cell_5_868_end:
__sbr_cell_5_869:
    shr ecx, 3
__sbr_cell_5_869_end:
__sbr_cell_5_870:
    mov edx, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_870_end:
__sbr_cell_5_871:
    bswap edx
__sbr_cell_5_871_end:
__sbr_cell_5_872:
    mov ecx, r8d
__sbr_cell_5_872_end:
__sbr_cell_5_873:
    and cl, 7
__sbr_cell_5_873_end:
__sbr_cell_5_874:
    shl edx, cl
__sbr_cell_5_874_end:
__sbr_cell_5_875:
    shr edx, 30
__sbr_cell_5_875_end:
ff_ps_read_data.Ld93:
__sbr_cell_5_876:
    add r8d, 2
__sbr_cell_5_876_end:
__sbr_cell_5_877:
    cmp r12d, r8d
__sbr_cell_5_877_end:
__sbr_cell_5_878:
    cmovb r8d, r12d
__sbr_cell_5_878_end:
__sbr_cell_5_879:
    mov ecx, 4294967294
__sbr_cell_5_879_end:
__sbr_cell_5_880:
    test edx, edx
__sbr_cell_5_880_end:
__sbr_cell_5_881:
    jne ff_ps_read_data.Ld70
__sbr_cell_5_881_end:
ff_ps_read_data.Lda7:
__sbr_cell_5_882:
    mov ecx, r8d
__sbr_cell_5_882_end:
__sbr_cell_5_883:
    shr ecx, 3
__sbr_cell_5_883_end:
__sbr_cell_5_884:
    xor edx, edx
__sbr_cell_5_884_end:
__sbr_cell_5_885:
    cmp r8d, r12d
__sbr_cell_5_885_end:
__sbr_cell_5_886:
    setl dl
__sbr_cell_5_886_end:
__sbr_cell_5_887:
    movzx esi, BYTE PTR [r13+rcx*1+0]
__sbr_cell_5_887_end:
__sbr_cell_5_888:
    mov ecx, r8d
__sbr_cell_5_888_end:
__sbr_cell_5_889:
    and cl, 7
__sbr_cell_5_889_end:
__sbr_cell_5_890:
    shl esi, cl
__sbr_cell_5_890_end:
__sbr_cell_5_891:
    add edx, r8d
__sbr_cell_5_891_end:
ff_ps_read_data.Ldc6:
__sbr_cell_5_892:
    shr esi, 7
__sbr_cell_5_892_end:
__sbr_cell_5_893:
    and esi, 1
__sbr_cell_5_893_end:
__sbr_cell_5_894:
    mov DWORD PTR [rbx+48], esi
__sbr_cell_5_894_end:
__sbr_cell_5_895:
    mov DWORD PTR [rbp-128], eax
__sbr_cell_5_895_end:
__sbr_cell_5_896:
    je ff_ps_read_data.Ld50
__sbr_cell_5_896_end:
ff_ps_read_data.Ldd8:
__sbr_cell_5_897:
    test r10b, r10b
__sbr_cell_5_897_end:
__sbr_cell_5_898:
    jle ff_ps_read_data.Ld50
__sbr_cell_5_898_end:
__sbr_cell_5_899:
    mov ebx, DWORD PTR [rbx+16]
__sbr_cell_5_899_end:
__sbr_cell_5_900:
    mov r9, QWORD PTR [rbp-120]
__sbr_cell_5_900_end:
__sbr_cell_5_901:
    mov r11, QWORD PTR [rbp-80]
__sbr_cell_5_901_end:
__sbr_cell_5_902:
    xor r15d, r15d
__sbr_cell_5_902_end:
__sbr_cell_5_903:
    jmp ff_ps_read_data.Le15
__sbr_cell_5_903_end:
__sbr_cell_5_904:
    .nops 1
__sbr_cell_5_904_end:
ff_ps_read_data.Le00:
__sbr_cell_5_905:
    inc r15
__sbr_cell_5_905_end:
__sbr_cell_5_906:
    add r11, 34
__sbr_cell_5_906_end:
__sbr_cell_5_907:
    add r9, 34
__sbr_cell_5_907_end:
__sbr_cell_5_908:
    cmp r15, QWORD PTR [rbp-88]
__sbr_cell_5_908_end:
__sbr_cell_5_909:
    je ff_ps_read_data.Ld50
__sbr_cell_5_909_end:
ff_ps_read_data.Le15:
__sbr_cell_5_910:
    mov ecx, edx
__sbr_cell_5_910_end:
__sbr_cell_5_911:
    shr ecx, 3
__sbr_cell_5_911_end:
__sbr_cell_5_912:
    xor esi, esi
__sbr_cell_5_912_end:
__sbr_cell_5_913:
    cmp edx, r12d
__sbr_cell_5_913_end:
__sbr_cell_5_914:
    setl sil
__sbr_cell_5_914_end:
__sbr_cell_5_915:
    add esi, edx
__sbr_cell_5_915_end:
__sbr_cell_5_916:
    movzx edi, BYTE PTR [r13+rcx*1+0]
__sbr_cell_5_916_end:
__sbr_cell_5_917:
    and dl, 7
__sbr_cell_5_917_end:
__sbr_cell_5_918:
    mov ecx, edx
__sbr_cell_5_918_end:
__sbr_cell_5_919:
    shl edi, cl
__sbr_cell_5_919_end:
ff_ps_read_data.Le32:
__sbr_cell_5_920:
    mov ecx, edi
__sbr_cell_5_920_end:
__sbr_cell_5_921:
    shr ecx, 4
__sbr_cell_5_921_end:
__sbr_cell_5_922:
    and ecx, 8
__sbr_cell_5_922_end:
__sbr_cell_5_923:
    lea rax, [rip+vlc_ps]
__sbr_cell_5_923_end:
__sbr_cell_5_924:
    mov rdx, QWORD PTR [rcx+rax*1+48]
__sbr_cell_5_924_end:
__sbr_cell_5_925:
    test dil, 128
__sbr_cell_5_925_end:
__sbr_cell_5_926:
    jne ff_ps_read_data.Leb0
__sbr_cell_5_926_end:
ff_ps_read_data.Le4c:
__sbr_cell_5_927:
    test ebx, ebx
__sbr_cell_5_927_end:
__sbr_cell_5_928:
    jle ff_ps_read_data.Lf29
__sbr_cell_5_928_end:
__sbr_cell_5_929:
    xor r14d, r14d
__sbr_cell_5_929_end:
__sbr_cell_5_930:
    xor r10d, r10d
__sbr_cell_5_930_end:
__sbr_cell_5_931:
    .nops 1
__sbr_cell_5_931_end:
ff_ps_read_data.Le60:
__sbr_cell_5_932:
    mov eax, esi
__sbr_cell_5_932_end:
__sbr_cell_5_933:
    shr eax, 3
__sbr_cell_5_933_end:
__sbr_cell_5_934:
    mov edi, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_934_end:
__sbr_cell_5_935:
    bswap edi
__sbr_cell_5_935_end:
__sbr_cell_5_936:
    mov ecx, esi
__sbr_cell_5_936_end:
__sbr_cell_5_937:
    and cl, 7
__sbr_cell_5_937_end:
__sbr_cell_5_938:
    shl edi, cl
__sbr_cell_5_938_end:
__sbr_cell_5_939:
    shr edi, 27
__sbr_cell_5_939_end:
__sbr_cell_5_940:
    cmp r14, 34
__sbr_cell_5_940_end:
__sbr_cell_5_941:
    je ff_ps_read_data.L175e
__sbr_cell_5_941_end:
ff_ps_read_data.Le80:
__sbr_cell_5_942:
    mov eax, edi
__sbr_cell_5_942_end:
__sbr_cell_5_943:
    movsx ecx, WORD PTR [rdx+rax*4+2]
__sbr_cell_5_943_end:
__sbr_cell_5_944:
    add esi, ecx
__sbr_cell_5_944_end:
__sbr_cell_5_945:
    cmp r12d, esi
__sbr_cell_5_945_end:
__sbr_cell_5_946:
    cmovb esi, r12d
__sbr_cell_5_946_end:
__sbr_cell_5_947:
    add r10b, BYTE PTR [rdx+rax*4+0]
__sbr_cell_5_947_end:
__sbr_cell_5_948:
    and r10b, 7
__sbr_cell_5_948_end:
__sbr_cell_5_949:
    mov BYTE PTR [r11+r14*1+0], r10b
__sbr_cell_5_949_end:
__sbr_cell_5_950:
    inc r14
__sbr_cell_5_950_end:
__sbr_cell_5_951:
    cmp rbx, r14
__sbr_cell_5_951_end:
__sbr_cell_5_952:
    jne ff_ps_read_data.Le60
__sbr_cell_5_952_end:
__sbr_cell_5_953:
    jmp ff_ps_read_data.Lf29
__sbr_cell_5_953_end:
__sbr_cell_5_954:
    .nops 1
__sbr_cell_5_954_end:
ff_ps_read_data.Leb0:
__sbr_cell_5_955:
    test ebx, ebx
__sbr_cell_5_955_end:
__sbr_cell_5_956:
    jle ff_ps_read_data.Lf29
__sbr_cell_5_956_end:
__sbr_cell_5_957:
    test r15, r15
__sbr_cell_5_957_end:
__sbr_cell_5_958:
    mov ecx, r15d
__sbr_cell_5_958_end:
__sbr_cell_5_959:
    cmove ecx, DWORD PTR [rbp-104]
__sbr_cell_5_959_end:
__sbr_cell_5_960:
    cmp ecx, 2
__sbr_cell_5_960_end:
__sbr_cell_5_961:
    mov eax, 1
__sbr_cell_5_961_end:
__sbr_cell_5_962:
    cmovl ecx, eax
__sbr_cell_5_962_end:
ff_ps_read_data.Lec9:
__sbr_cell_5_963:
    mov rdi, rcx
__sbr_cell_5_963_end:
__sbr_cell_5_964:
    shl rdi, 5
__sbr_cell_5_964_end:
__sbr_cell_5_965:
    lea r14, [rdi+rcx*2+0]
__sbr_cell_5_965_end:
__sbr_cell_5_966:
    add r14, QWORD PTR [rbp-80]
__sbr_cell_5_966_end:
__sbr_cell_5_967:
    mov edi, esi
__sbr_cell_5_967_end:
__sbr_cell_5_968:
    xor r10d, r10d
__sbr_cell_5_968_end:
__sbr_cell_5_969:
    .nops 1
__sbr_cell_5_969_end:
ff_ps_read_data.Lee0:
__sbr_cell_5_970:
    cmp r10, 34
__sbr_cell_5_970_end:
__sbr_cell_5_971:
    je ff_ps_read_data.L1759
__sbr_cell_5_971_end:
__sbr_cell_5_972:
    movzx eax, BYTE PTR [r14+r10*1-34]
__sbr_cell_5_972_end:
__sbr_cell_5_973:
    mov ecx, edi
__sbr_cell_5_973_end:
__sbr_cell_5_974:
    shr ecx, 3
__sbr_cell_5_974_end:
__sbr_cell_5_975:
    mov esi, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_975_end:
__sbr_cell_5_976:
    bswap esi
__sbr_cell_5_976_end:
__sbr_cell_5_977:
    mov ecx, edi
__sbr_cell_5_977_end:
__sbr_cell_5_978:
    and cl, 7
__sbr_cell_5_978_end:
__sbr_cell_5_979:
    shl esi, cl
__sbr_cell_5_979_end:
__sbr_cell_5_980:
    shr esi, 27
__sbr_cell_5_980_end:
ff_ps_read_data.Lf06:
__sbr_cell_5_981:
    mov ecx, esi
__sbr_cell_5_981_end:
__sbr_cell_5_982:
    movsx esi, WORD PTR [rdx+rcx*4+2]
__sbr_cell_5_982_end:
__sbr_cell_5_983:
    add esi, edi
__sbr_cell_5_983_end:
__sbr_cell_5_984:
    cmp r12d, esi
__sbr_cell_5_984_end:
__sbr_cell_5_985:
    cmovb esi, r12d
__sbr_cell_5_985_end:
__sbr_cell_5_986:
    add al, BYTE PTR [rdx+rcx*4+0]
__sbr_cell_5_986_end:
__sbr_cell_5_987:
    and al, 7
__sbr_cell_5_987_end:
__sbr_cell_5_988:
    mov BYTE PTR [r11+r10*1+0], al
__sbr_cell_5_988_end:
__sbr_cell_5_989:
    inc r10
__sbr_cell_5_989_end:
__sbr_cell_5_990:
    mov edi, esi
__sbr_cell_5_990_end:
__sbr_cell_5_991:
    cmp rbx, r10
__sbr_cell_5_991_end:
__sbr_cell_5_992:
    jne ff_ps_read_data.Lee0
__sbr_cell_5_992_end:
ff_ps_read_data.Lf29:
__sbr_cell_5_993:
    mov eax, esi
__sbr_cell_5_993_end:
__sbr_cell_5_994:
    shr eax, 3
__sbr_cell_5_994_end:
__sbr_cell_5_995:
    xor edx, edx
__sbr_cell_5_995_end:
__sbr_cell_5_996:
    cmp esi, r12d
__sbr_cell_5_996_end:
__sbr_cell_5_997:
    setl dl
__sbr_cell_5_997_end:
__sbr_cell_5_998:
    add edx, esi
__sbr_cell_5_998_end:
__sbr_cell_5_999:
    movzx eax, BYTE PTR [r13+rax*1+0]
__sbr_cell_5_999_end:
__sbr_cell_5_1000:
    and sil, 7
__sbr_cell_5_1000_end:
__sbr_cell_5_1001:
    mov ecx, esi
__sbr_cell_5_1001_end:
__sbr_cell_5_1002:
    shl eax, cl
__sbr_cell_5_1002_end:
ff_ps_read_data.Lf46:
__sbr_cell_5_1003:
    mov ecx, eax
__sbr_cell_5_1003_end:
__sbr_cell_5_1004:
    shr ecx, 4
__sbr_cell_5_1004_end:
__sbr_cell_5_1005:
    and ecx, 8
__sbr_cell_5_1005_end:
__sbr_cell_5_1006:
    lea rsi, [rip+vlc_ps]
__sbr_cell_5_1006_end:
__sbr_cell_5_1007:
    mov rsi, QWORD PTR [rcx+rsi*1+64]
__sbr_cell_5_1007_end:
__sbr_cell_5_1008:
    test al, 128
__sbr_cell_5_1008_end:
__sbr_cell_5_1009:
    jne ff_ps_read_data.Lfc0
__sbr_cell_5_1009_end:
ff_ps_read_data.Lf5e:
__sbr_cell_5_1010:
    test ebx, ebx
__sbr_cell_5_1010_end:
__sbr_cell_5_1011:
    jle ff_ps_read_data.Le00
__sbr_cell_5_1011_end:
__sbr_cell_5_1012:
    xor r14d, r14d
__sbr_cell_5_1012_end:
__sbr_cell_5_1013:
    xor r10d, r10d
__sbr_cell_5_1013_end:
__sbr_cell_5_1014:
    .nops 1
__sbr_cell_5_1014_end:
ff_ps_read_data.Lf70:
__sbr_cell_5_1015:
    mov eax, edx
__sbr_cell_5_1015_end:
__sbr_cell_5_1016:
    shr eax, 3
__sbr_cell_5_1016_end:
__sbr_cell_5_1017:
    mov edi, DWORD PTR [r13+rax*1+0]
__sbr_cell_5_1017_end:
__sbr_cell_5_1018:
    bswap edi
__sbr_cell_5_1018_end:
__sbr_cell_5_1019:
    mov ecx, edx
__sbr_cell_5_1019_end:
__sbr_cell_5_1020:
    and cl, 7
__sbr_cell_5_1020_end:
__sbr_cell_5_1021:
    shl edi, cl
__sbr_cell_5_1021_end:
__sbr_cell_5_1022:
    shr edi, 27
__sbr_cell_5_1022_end:
__sbr_cell_5_1023:
    cmp r14, 34
__sbr_cell_5_1023_end:
__sbr_cell_5_1024:
    je ff_ps_read_data.L1768
__sbr_cell_5_1024_end:
ff_ps_read_data.Lf90:
__sbr_cell_5_1025:
    mov eax, edi
__sbr_cell_5_1025_end:
__sbr_cell_5_1026:
    movsx ecx, WORD PTR [rsi+rax*4+2]
__sbr_cell_5_1026_end:
__sbr_cell_5_1027:
    add edx, ecx
__sbr_cell_5_1027_end:
__sbr_cell_5_1028:
    cmp r12d, edx
__sbr_cell_5_1028_end:
__sbr_cell_5_1029:
    cmovb edx, r12d
__sbr_cell_5_1029_end:
__sbr_cell_5_1030:
    add r10b, BYTE PTR [rsi+rax*4+0]
__sbr_cell_5_1030_end:
__sbr_cell_5_1031:
    and r10b, 7
__sbr_cell_5_1031_end:
__sbr_cell_5_1032:
    mov BYTE PTR [r9+r14*1+0], r10b
__sbr_cell_5_1032_end:
__sbr_cell_5_1033:
    inc r14
__sbr_cell_5_1033_end:
__sbr_cell_5_1034:
    cmp rbx, r14
__sbr_cell_5_1034_end:
__sbr_cell_5_1035:
    jne ff_ps_read_data.Lf70
__sbr_cell_5_1035_end:
__sbr_cell_5_1036:
    jmp ff_ps_read_data.Le00
__sbr_cell_5_1036_end:
__sbr_cell_5_1037:
    .nops 1
__sbr_cell_5_1037_end:
ff_ps_read_data.Lfc0:
__sbr_cell_5_1038:
    test ebx, ebx
__sbr_cell_5_1038_end:
__sbr_cell_5_1039:
    jle ff_ps_read_data.Le00
__sbr_cell_5_1039_end:
__sbr_cell_5_1040:
    test r15, r15
__sbr_cell_5_1040_end:
__sbr_cell_5_1041:
    mov eax, r15d
__sbr_cell_5_1041_end:
__sbr_cell_5_1042:
    cmove eax, DWORD PTR [rbp-104]
__sbr_cell_5_1042_end:
__sbr_cell_5_1043:
    cmp eax, 2
__sbr_cell_5_1043_end:
__sbr_cell_5_1044:
    mov ecx, 1
__sbr_cell_5_1044_end:
__sbr_cell_5_1045:
    cmovl eax, ecx
__sbr_cell_5_1045_end:
ff_ps_read_data.Lfdd:
__sbr_cell_5_1046:
    mov rcx, rax
__sbr_cell_5_1046_end:
__sbr_cell_5_1047:
    shl rcx, 5
__sbr_cell_5_1047_end:
__sbr_cell_5_1048:
    lea r14, [rcx+rax*2+0]
__sbr_cell_5_1048_end:
__sbr_cell_5_1049:
    add r14, QWORD PTR [rbp-120]
__sbr_cell_5_1049_end:
__sbr_cell_5_1050:
    mov edi, edx
__sbr_cell_5_1050_end:
__sbr_cell_5_1051:
    xor r10d, r10d
__sbr_cell_5_1051_end:
__sbr_cell_5_1052:
    .nops 1
__sbr_cell_5_1052_end:
ff_ps_read_data.L1000:
__sbr_cell_5_1053:
    cmp r10, 34
__sbr_cell_5_1053_end:
__sbr_cell_5_1054:
    je ff_ps_read_data.L1763
__sbr_cell_5_1054_end:
__sbr_cell_5_1055:
    movzx eax, BYTE PTR [r14+r10*1-34]
__sbr_cell_5_1055_end:
__sbr_cell_5_1056:
    mov ecx, edi
__sbr_cell_5_1056_end:
__sbr_cell_5_1057:
    shr ecx, 3
__sbr_cell_5_1057_end:
__sbr_cell_5_1058:
    mov edx, DWORD PTR [r13+rcx*1+0]
__sbr_cell_5_1058_end:
__sbr_cell_5_1059:
    bswap edx
__sbr_cell_5_1059_end:
__sbr_cell_5_1060:
    mov ecx, edi
__sbr_cell_5_1060_end:
__sbr_cell_5_1061:
    and cl, 7
__sbr_cell_5_1061_end:
__sbr_cell_5_1062:
    shl edx, cl
__sbr_cell_5_1062_end:
__sbr_cell_5_1063:
    shr edx, 27
__sbr_cell_5_1063_end:
ff_ps_read_data.L1026:
__sbr_cell_5_1064:
    mov ecx, edx
__sbr_cell_5_1064_end:
__sbr_cell_5_1065:
    movsx edx, WORD PTR [rsi+rcx*4+2]
__sbr_cell_5_1065_end:
__sbr_cell_5_1066:
    add edx, edi
__sbr_cell_5_1066_end:
__sbr_cell_5_1067:
    cmp r12d, edx
__sbr_cell_5_1067_end:
__sbr_cell_5_1068:
    cmovb edx, r12d
__sbr_cell_5_1068_end:
__sbr_cell_5_1069:
    add al, BYTE PTR [rsi+rcx*4+0]
__sbr_cell_5_1069_end:
__sbr_cell_5_1070:
    and al, 7
__sbr_cell_5_1070_end:
__sbr_cell_5_1071:
    mov BYTE PTR [r9+r10*1+0], al
__sbr_cell_5_1071_end:
__sbr_cell_5_1072:
    inc r10
__sbr_cell_5_1072_end:
__sbr_cell_5_1073:
    mov edi, edx
__sbr_cell_5_1073_end:
__sbr_cell_5_1074:
    cmp rbx, r10
__sbr_cell_5_1074_end:
__sbr_cell_5_1075:
    jne ff_ps_read_data.L1000
__sbr_cell_5_1075_end:
__sbr_cell_5_1076:
    jmp ff_ps_read_data.Le00
__sbr_cell_5_1076_end:
ff_ps_read_data.L104e:
__sbr_cell_5_1077:
    test eax, eax
__sbr_cell_5_1077_end:
__sbr_cell_5_1078:
    js ff_ps_read_data.L1459
__sbr_cell_5_1078_end:
__sbr_cell_5_1079:
    add eax, r8d
__sbr_cell_5_1079_end:
__sbr_cell_5_1080:
    cmp r12d, eax
__sbr_cell_5_1080_end:
__sbr_cell_5_1081:
    cmovb eax, r12d
__sbr_cell_5_1081_end:
__sbr_cell_5_1082:
    mov r8d, eax
__sbr_cell_5_1082_end:
ff_ps_read_data.L1063:
__sbr_cell_5_1083:
    mov r15d, DWORD PTR [rbp-44]
__sbr_cell_5_1083_end:
__sbr_cell_5_1084:
    mov eax, DWORD PTR [rbx+48]
__sbr_cell_5_1084_end:
__sbr_cell_5_1085:
    and eax, 1
__sbr_cell_5_1085_end:
__sbr_cell_5_1086:
    mov DWORD PTR [rbx+48], eax
__sbr_cell_5_1086_end:
__sbr_cell_5_1087:
    test r10, r10
__sbr_cell_5_1087_end:
__sbr_cell_5_1088:
    mov r12, QWORD PTR [rbp-72]
__sbr_cell_5_1088_end:
__sbr_cell_5_1089:
    mov r9, QWORD PTR [rbp-104]
__sbr_cell_5_1089_end:
__sbr_cell_5_1090:
    mov r13d, DWORD PTR [rbp-132]
__sbr_cell_5_1090_end:
__sbr_cell_5_1091:
    je ff_ps_read_data.L10f6
__sbr_cell_5_1091_end:
ff_ps_read_data.L1084:
__sbr_cell_5_1092:
    cmp r12b, 6
__sbr_cell_5_1092_end:
__sbr_cell_5_1093:
    mov r10d, DWORD PTR [rbp-108]
__sbr_cell_5_1093_end:
__sbr_cell_5_1094:
    jae ff_ps_read_data.L17b3
__sbr_cell_5_1094_end:
__sbr_cell_5_1095:
    mov ecx, r12d
__sbr_cell_5_1095_end:
__sbr_cell_5_1096:
    cmp DWORD PTR [rbx+rcx*4+52], 31
__sbr_cell_5_1096_end:
__sbr_cell_5_1097:
    mov r9d, r12d
__sbr_cell_5_1097_end:
__sbr_cell_5_1098:
    jl ff_ps_read_data.L1104
__sbr_cell_5_1098_end:
__sbr_cell_5_1099:
    mov ecx, DWORD PTR [rbx+756]
__sbr_cell_5_1099_end:
__sbr_cell_5_1100:
    mov DWORD PTR [rbx+760], ecx
__sbr_cell_5_1100_end:
__sbr_cell_5_1101:
    test r10d, r10d
__sbr_cell_5_1101_end:
__sbr_cell_5_1102:
    je ff_ps_read_data.L1380
__sbr_cell_5_1102_end:
ff_ps_read_data.L10b4:
__sbr_cell_5_1103:
    cmp DWORD PTR [rbx+12], 34
__sbr_cell_5_1103_end:
__sbr_cell_5_1104:
    sete cl
__sbr_cell_5_1104_end:
__sbr_cell_5_1105:
    je ff_ps_read_data.L138c
__sbr_cell_5_1105_end:
__sbr_cell_5_1106:
    test r13d, r13d
__sbr_cell_5_1106_end:
__sbr_cell_5_1107:
    jne ff_ps_read_data.L1385
__sbr_cell_5_1107_end:
__sbr_cell_5_1108:
    jmp ff_ps_read_data.L138c
__sbr_cell_5_1108_end:
ff_ps_read_data.L10cf:
__sbr_cell_5_1109:
    lea rdx, [rip+L_str_8]
__sbr_cell_5_1109_end:
ff_ps_read_data.L10d6:
__sbr_cell_5_1110:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_5_1110_end:
__sbr_cell_5_1111:
    mov esi, 16
__sbr_cell_5_1111_end:
__sbr_cell_5_1112:
    xor eax, eax
__sbr_cell_5_1112_end:
__sbr_cell_5_1113:
    vzeroupper
__sbr_cell_5_1113_end:
__sbr_cell_5_1114:
    call av_log
__sbr_cell_5_1114_end:
__sbr_cell_5_1115:
    mov r15d, DWORD PTR [rbp-44]
__sbr_cell_5_1115_end:
__sbr_cell_5_1116:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_5_1116_end:
__sbr_cell_5_1117:
    jmp ff_ps_read_data.L1479
__sbr_cell_5_1117_end:
ff_ps_read_data.L10f6:
__sbr_cell_5_1118:
    cmp r9d, 2
__sbr_cell_5_1118_end:
__sbr_cell_5_1119:
    mov r10d, DWORD PTR [rbp-108]
__sbr_cell_5_1119_end:
__sbr_cell_5_1120:
    jl ff_ps_read_data.L11fd
__sbr_cell_5_1120_end:
ff_ps_read_data.L1104:
__sbr_cell_5_1121:
    lea ecx, [r9-1]
__sbr_cell_5_1121_end:
__sbr_cell_5_1122:
    mov ecx, ecx
__sbr_cell_5_1122_end:
__sbr_cell_5_1123:
    test r10d, r10d
__sbr_cell_5_1123_end:
__sbr_cell_5_1124:
    je ff_ps_read_data.L1148
__sbr_cell_5_1124_end:
__sbr_cell_5_1125:
    cmp r9d, 7
__sbr_cell_5_1125_end:
__sbr_cell_5_1126:
    jae ff_ps_read_data.L17bd
__sbr_cell_5_1126_end:
ff_ps_read_data.L1119:
__sbr_cell_5_1127:
    mov edx, r12d
__sbr_cell_5_1127_end:
__sbr_cell_5_1128:
    mov rsi, rdx
__sbr_cell_5_1128_end:
__sbr_cell_5_1129:
    shl rsi, 5
__sbr_cell_5_1129_end:
__sbr_cell_5_1130:
    lea rdx, [rsi+rdx*2+0]
__sbr_cell_5_1130_end:
__sbr_cell_5_1131:
    mov rsi, rcx
__sbr_cell_5_1131_end:
__sbr_cell_5_1132:
    shl rsi, 5
__sbr_cell_5_1132_end:
__sbr_cell_5_1133:
    lea rsi, [rsi+rcx*2+0]
__sbr_cell_5_1133_end:
__sbr_cell_5_1134:
    movzx edi, WORD PTR [rbx+rsi*1+108]
__sbr_cell_5_1134_end:
__sbr_cell_5_1135:
    mov WORD PTR [rbx+rdx*1+108], di
__sbr_cell_5_1135_end:
__sbr_cell_5_1136:
    vmovdqu ymm0, YMMWORD PTR [rbx+rsi*1+76]
__sbr_cell_5_1136_end:
__sbr_cell_5_1137:
    vmovdqu YMMWORD PTR [rbx+rdx*1+76], ymm0
__sbr_cell_5_1137_end:
ff_ps_read_data.L1148:
__sbr_cell_5_1138:
    test r13d, r13d
__sbr_cell_5_1138_end:
__sbr_cell_5_1139:
    je ff_ps_read_data.L1192
__sbr_cell_5_1139_end:
__sbr_cell_5_1140:
    cmp r9d, 7
__sbr_cell_5_1140_end:
__sbr_cell_5_1141:
    jae ff_ps_read_data.L17c2
__sbr_cell_5_1141_end:
ff_ps_read_data.L1157:
__sbr_cell_5_1142:
    mov edx, r12d
__sbr_cell_5_1142_end:
__sbr_cell_5_1143:
    mov rsi, rdx
__sbr_cell_5_1143_end:
__sbr_cell_5_1144:
    shl rsi, 5
__sbr_cell_5_1144_end:
__sbr_cell_5_1145:
    lea rdx, [rsi+rdx*2+0]
__sbr_cell_5_1145_end:
__sbr_cell_5_1146:
    mov rsi, rcx
__sbr_cell_5_1146_end:
__sbr_cell_5_1147:
    shl rsi, 5
__sbr_cell_5_1147_end:
__sbr_cell_5_1148:
    lea rsi, [rsi+rcx*2+0]
__sbr_cell_5_1148_end:
__sbr_cell_5_1149:
    movzx edi, WORD PTR [rbx+rsi*1+278]
__sbr_cell_5_1149_end:
__sbr_cell_5_1150:
    mov WORD PTR [rbx+rdx*1+278], di
__sbr_cell_5_1150_end:
__sbr_cell_5_1151:
    vmovdqu ymm0, YMMWORD PTR [rbx+rsi*1+246]
__sbr_cell_5_1151_end:
__sbr_cell_5_1152:
    vmovdqu YMMWORD PTR [rbx+rdx*1+246], ymm0
__sbr_cell_5_1152_end:
ff_ps_read_data.L1192:
__sbr_cell_5_1153:
    test eax, eax
__sbr_cell_5_1153_end:
__sbr_cell_5_1154:
    je ff_ps_read_data.L11fd
__sbr_cell_5_1154_end:
__sbr_cell_5_1155:
    cmp r9d, 7
__sbr_cell_5_1155_end:
__sbr_cell_5_1156:
    jae ff_ps_read_data.L17cc
__sbr_cell_5_1156_end:
ff_ps_read_data.L11a0:
__sbr_cell_5_1157:
    mov edx, r12d
__sbr_cell_5_1157_end:
__sbr_cell_5_1158:
    mov rsi, rdx
__sbr_cell_5_1158_end:
__sbr_cell_5_1159:
    shl rsi, 5
__sbr_cell_5_1159_end:
__sbr_cell_5_1160:
    lea rdx, [rsi+rdx*2+0]
__sbr_cell_5_1160_end:
__sbr_cell_5_1161:
    mov rsi, rcx
__sbr_cell_5_1161_end:
__sbr_cell_5_1162:
    shl rsi, 5
__sbr_cell_5_1162_end:
__sbr_cell_5_1163:
    lea rcx, [rsi+rcx*2+0]
__sbr_cell_5_1163_end:
__sbr_cell_5_1164:
    movzx esi, WORD PTR [rbx+rcx*1+448]
__sbr_cell_5_1164_end:
__sbr_cell_5_1165:
    mov WORD PTR [rbx+rdx*1+448], si
__sbr_cell_5_1165_end:
__sbr_cell_5_1166:
    vmovups ymm0, YMMWORD PTR [rbx+rcx*1+416]
__sbr_cell_5_1166_end:
__sbr_cell_5_1167:
    vmovups YMMWORD PTR [rbx+rdx*1+416], ymm0
__sbr_cell_5_1167_end:
ff_ps_read_data.L11db:
__sbr_cell_5_1168:
    movzx esi, WORD PTR [rbx+rcx*1+618]
__sbr_cell_5_1168_end:
__sbr_cell_5_1169:
    mov WORD PTR [rbx+rdx*1+618], si
__sbr_cell_5_1169_end:
__sbr_cell_5_1170:
    vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1+586]
__sbr_cell_5_1170_end:
__sbr_cell_5_1171:
    vmovdqu YMMWORD PTR [rbx+rdx*1+586], ymm0
__sbr_cell_5_1171_end:
ff_ps_read_data.L11fd:
__sbr_cell_5_1172:
    test r10d, r10d
__sbr_cell_5_1172_end:
__sbr_cell_5_1173:
    je ff_ps_read_data.L12ef
__sbr_cell_5_1173_end:
__sbr_cell_5_1174:
    mov rcx, QWORD PTR [rbp-56]
__sbr_cell_5_1174_end:
__sbr_cell_5_1175:
    mov ecx, DWORD PTR [rcx+12]
__sbr_cell_5_1175_end:
__sbr_cell_5_1176:
    test ecx, ecx
__sbr_cell_5_1176_end:
__sbr_cell_5_1177:
    jle ff_ps_read_data.L12ef
__sbr_cell_5_1177_end:
__sbr_cell_5_1178:
    cmp BYTE PTR [rbp-96], 4
__sbr_cell_5_1178_end:
__sbr_cell_5_1179:
    ja ff_ps_read_data.L17c7
__sbr_cell_5_1179_end:
ff_ps_read_data.L121f:
__sbr_cell_5_1180:
    mov edi, r12d
__sbr_cell_5_1180_end:
__sbr_cell_5_1181:
    mov r10, QWORD PTR [rbp-56]
__sbr_cell_5_1181_end:
__sbr_cell_5_1182:
    mov edx, DWORD PTR [r10+8]
__sbr_cell_5_1182_end:
__sbr_cell_5_1183:
    lea edx, [rdx*8+7]
__sbr_cell_5_1183_end:
__sbr_cell_5_1184:
    lea rsi, [rcx-3]
__sbr_cell_5_1184_end:
__sbr_cell_5_1185:
    mov r9, rdi
__sbr_cell_5_1185_end:
ff_ps_read_data.L1238:
__sbr_cell_5_1186:
    shl r9, 5
__sbr_cell_5_1186_end:
__sbr_cell_5_1187:
    lea rdi, [r9+rdi*2+0]
__sbr_cell_5_1187_end:
__sbr_cell_5_1188:
    add rdi, r10
__sbr_cell_5_1188_end:
__sbr_cell_5_1189:
    add rdi, 79
__sbr_cell_5_1189_end:
__sbr_cell_5_1190:
    lea r9, [rcx-2]
__sbr_cell_5_1190_end:
__sbr_cell_5_1191:
    lea r10, [rcx-1]
__sbr_cell_5_1191_end:
__sbr_cell_5_1192:
    xor r11d, r11d
__sbr_cell_5_1192_end:
ff_ps_read_data.L1252:
__sbr_cell_5_1193:
    movzx ebx, BYTE PTR [rdi+r11*1-3]
__sbr_cell_5_1193_end:
__sbr_cell_5_1194:
    mov r14d, ebx
__sbr_cell_5_1194_end:
__sbr_cell_5_1195:
    sar r14b, 7
__sbr_cell_5_1195_end:
__sbr_cell_5_1196:
    xor bl, r14b
__sbr_cell_5_1196_end:
__sbr_cell_5_1197:
    sub bl, r14b
__sbr_cell_5_1197_end:
__sbr_cell_5_1198:
    movzx ebx, bl
__sbr_cell_5_1198_end:
__sbr_cell_5_1199:
    cmp edx, ebx
__sbr_cell_5_1199_end:
__sbr_cell_5_1200:
    jl ff_ps_read_data.L14cc
__sbr_cell_5_1200_end:
__sbr_cell_5_1201:
    cmp r10, r11
__sbr_cell_5_1201_end:
__sbr_cell_5_1202:
    je ff_ps_read_data.L12ef
__sbr_cell_5_1202_end:
ff_ps_read_data.L1275:
__sbr_cell_5_1203:
    movzx ebx, BYTE PTR [rdi+r11*1-2]
__sbr_cell_5_1203_end:
__sbr_cell_5_1204:
    mov r14d, ebx
__sbr_cell_5_1204_end:
__sbr_cell_5_1205:
    sar r14b, 7
__sbr_cell_5_1205_end:
__sbr_cell_5_1206:
    xor bl, r14b
__sbr_cell_5_1206_end:
__sbr_cell_5_1207:
    sub bl, r14b
__sbr_cell_5_1207_end:
__sbr_cell_5_1208:
    movzx ebx, bl
__sbr_cell_5_1208_end:
__sbr_cell_5_1209:
    cmp edx, ebx
__sbr_cell_5_1209_end:
__sbr_cell_5_1210:
    jl ff_ps_read_data.L14cc
__sbr_cell_5_1210_end:
__sbr_cell_5_1211:
    cmp r9, r11
__sbr_cell_5_1211_end:
__sbr_cell_5_1212:
    je ff_ps_read_data.L12ef
__sbr_cell_5_1212_end:
ff_ps_read_data.L1298:
__sbr_cell_5_1213:
    cmp r11, 32
__sbr_cell_5_1213_end:
__sbr_cell_5_1214:
    je ff_ps_read_data.L17a4
__sbr_cell_5_1214_end:
__sbr_cell_5_1215:
    movzx ebx, BYTE PTR [rdi+r11*1-1]
__sbr_cell_5_1215_end:
__sbr_cell_5_1216:
    mov r14d, ebx
__sbr_cell_5_1216_end:
__sbr_cell_5_1217:
    sar r14b, 7
__sbr_cell_5_1217_end:
__sbr_cell_5_1218:
    xor bl, r14b
__sbr_cell_5_1218_end:
__sbr_cell_5_1219:
    sub bl, r14b
__sbr_cell_5_1219_end:
__sbr_cell_5_1220:
    movzx ebx, bl
__sbr_cell_5_1220_end:
__sbr_cell_5_1221:
    cmp edx, ebx
__sbr_cell_5_1221_end:
__sbr_cell_5_1222:
    jl ff_ps_read_data.L14cc
__sbr_cell_5_1222_end:
__sbr_cell_5_1223:
    cmp rsi, r11
__sbr_cell_5_1223_end:
__sbr_cell_5_1224:
    je ff_ps_read_data.L12ef
__sbr_cell_5_1224_end:
ff_ps_read_data.L12c5:
__sbr_cell_5_1225:
    movzx ebx, BYTE PTR [rdi+r11*1+0]
__sbr_cell_5_1225_end:
__sbr_cell_5_1226:
    mov r14d, ebx
__sbr_cell_5_1226_end:
__sbr_cell_5_1227:
    sar r14b, 7
__sbr_cell_5_1227_end:
__sbr_cell_5_1228:
    xor bl, r14b
__sbr_cell_5_1228_end:
__sbr_cell_5_1229:
    sub bl, r14b
__sbr_cell_5_1229_end:
__sbr_cell_5_1230:
    movzx ebx, bl
__sbr_cell_5_1230_end:
__sbr_cell_5_1231:
    cmp edx, ebx
__sbr_cell_5_1231_end:
__sbr_cell_5_1232:
    jl ff_ps_read_data.L14cc
__sbr_cell_5_1232_end:
__sbr_cell_5_1233:
    add r11, 4
__sbr_cell_5_1233_end:
__sbr_cell_5_1234:
    cmp rcx, r11
__sbr_cell_5_1234_end:
__sbr_cell_5_1235:
    jne ff_ps_read_data.L1252
__sbr_cell_5_1235_end:
ff_ps_read_data.L12ef:
__sbr_cell_5_1236:
    test r13d, r13d
__sbr_cell_5_1236_end:
__sbr_cell_5_1237:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_5_1237_end:
__sbr_cell_5_1238:
    je ff_ps_read_data.L1349
__sbr_cell_5_1238_end:
__sbr_cell_5_1239:
    mov ecx, DWORD PTR [rbx+12]
__sbr_cell_5_1239_end:
__sbr_cell_5_1240:
    test ecx, ecx
__sbr_cell_5_1240_end:
__sbr_cell_5_1241:
    jle ff_ps_read_data.L1349
__sbr_cell_5_1241_end:
ff_ps_read_data.L12ff:
__sbr_cell_5_1242:
    cmp BYTE PTR [rbp-96], 4
__sbr_cell_5_1242_end:
__sbr_cell_5_1243:
    ja ff_ps_read_data.L17d1
__sbr_cell_5_1243_end:
__sbr_cell_5_1244:
    mov edx, r12d
__sbr_cell_5_1244_end:
__sbr_cell_5_1245:
    mov rsi, rdx
__sbr_cell_5_1245_end:
__sbr_cell_5_1246:
    shl rsi, 5
__sbr_cell_5_1246_end:
__sbr_cell_5_1247:
    lea rdx, [rsi+rdx*2+0]
__sbr_cell_5_1247_end:
__sbr_cell_5_1248:
    add rdx, rbx
__sbr_cell_5_1248_end:
__sbr_cell_5_1249:
    add rdx, 246
__sbr_cell_5_1249_end:
__sbr_cell_5_1250:
    cmp BYTE PTR [rdx+0], 7
__sbr_cell_5_1250_end:
__sbr_cell_5_1251:
    jbe ff_ps_read_data.L14ec
__sbr_cell_5_1251_end:
ff_ps_read_data.L132a:
__sbr_cell_5_1252:
    lea rdx, [rip+L_str_5]
__sbr_cell_5_1252_end:
__sbr_cell_5_1253:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_5_1253_end:
__sbr_cell_5_1254:
    mov esi, 16
__sbr_cell_5_1254_end:
__sbr_cell_5_1255:
    xor eax, eax
__sbr_cell_5_1255_end:
__sbr_cell_5_1256:
    vzeroupper
__sbr_cell_5_1256_end:
__sbr_cell_5_1257:
    call av_log
__sbr_cell_5_1257_end:
__sbr_cell_5_1258:
    jmp ff_ps_read_data.L1479
__sbr_cell_5_1258_end:
ff_ps_read_data.L1349:
__sbr_cell_5_1259:
    mov ecx, r12d
__sbr_cell_5_1259_end:
__sbr_cell_5_1260:
    inc r12d
__sbr_cell_5_1260_end:
__sbr_cell_5_1261:
    mov DWORD PTR [rbx+44], r12d
__sbr_cell_5_1261_end:
__sbr_cell_5_1262:
    cmp cl, 5
__sbr_cell_5_1262_end:
__sbr_cell_5_1263:
    jae ff_ps_read_data.L17b8
__sbr_cell_5_1263_end:
ff_ps_read_data.L135c:
__sbr_cell_5_1264:
    mov ecx, r12d
__sbr_cell_5_1264_end:
__sbr_cell_5_1265:
    mov DWORD PTR [rbx+rcx*4+52], 31
__sbr_cell_5_1265_end:
__sbr_cell_5_1266:
    mov r10d, DWORD PTR [rbx+4]
__sbr_cell_5_1266_end:
__sbr_cell_5_1267:
    mov ecx, DWORD PTR [rbx+756]
__sbr_cell_5_1267_end:
__sbr_cell_5_1268:
    mov DWORD PTR [rbx+760], ecx
__sbr_cell_5_1268_end:
__sbr_cell_5_1269:
    test r10d, r10d
__sbr_cell_5_1269_end:
__sbr_cell_5_1270:
    jne ff_ps_read_data.L10b4
__sbr_cell_5_1270_end:
ff_ps_read_data.L1380:
__sbr_cell_5_1271:
    test r13d, r13d
__sbr_cell_5_1271_end:
__sbr_cell_5_1272:
    je ff_ps_read_data.L1395
__sbr_cell_5_1272_end:
ff_ps_read_data.L1385:
__sbr_cell_5_1273:
    cmp DWORD PTR [rbx+28], 34
__sbr_cell_5_1273_end:
__sbr_cell_5_1274:
    sete cl
__sbr_cell_5_1274_end:
ff_ps_read_data.L138c:
__sbr_cell_5_1275:
    movzx ecx, cl
__sbr_cell_5_1275_end:
__sbr_cell_5_1276:
    mov DWORD PTR [rbx+756], ecx
__sbr_cell_5_1276_end:
ff_ps_read_data.L1395:
__sbr_cell_5_1277:
    test eax, eax
__sbr_cell_5_1277_end:
__sbr_cell_5_1278:
    jne ff_ps_read_data.L13f5
__sbr_cell_5_1278_end:
__sbr_cell_5_1279:
    vpxor xmm0, xmm0, xmm0
__sbr_cell_5_1279_end:
__sbr_cell_5_1280:
    vmovdqu YMMWORD PTR [rbx+724], ymm0
__sbr_cell_5_1280_end:
__sbr_cell_5_1281:
    vmovdqu YMMWORD PTR [rbx+704], ymm0
__sbr_cell_5_1281_end:
ff_ps_read_data.L13ad:
__sbr_cell_5_1282:
    vmovdqu YMMWORD PTR [rbx+672], ymm0
__sbr_cell_5_1282_end:
__sbr_cell_5_1283:
    vmovdqu YMMWORD PTR [rbx+640], ymm0
__sbr_cell_5_1283_end:
ff_ps_read_data.L13bd:
__sbr_cell_5_1284:
    vmovdqu YMMWORD PTR [rbx+608], ymm0
__sbr_cell_5_1284_end:
__sbr_cell_5_1285:
    vmovdqu YMMWORD PTR [rbx+576], ymm0
__sbr_cell_5_1285_end:
ff_ps_read_data.L13cd:
__sbr_cell_5_1286:
    vmovdqu YMMWORD PTR [rbx+544], ymm0
__sbr_cell_5_1286_end:
__sbr_cell_5_1287:
    vmovdqu YMMWORD PTR [rbx+512], ymm0
__sbr_cell_5_1287_end:
ff_ps_read_data.L13dd:
__sbr_cell_5_1288:
    vmovdqu YMMWORD PTR [rbx+480], ymm0
__sbr_cell_5_1288_end:
__sbr_cell_5_1289:
    vmovdqu YMMWORD PTR [rbx+448], ymm0
__sbr_cell_5_1289_end:
ff_ps_read_data.L13ed:
__sbr_cell_5_1290:
    vmovdqu YMMWORD PTR [rbx+416], ymm0
__sbr_cell_5_1290_end:
ff_ps_read_data.L13f5:
__sbr_cell_5_1291:
    cmp DWORD PTR [rbp-136], 0
__sbr_cell_5_1291_end:
__sbr_cell_5_1292:
    je ff_ps_read_data.L1404
__sbr_cell_5_1292_end:
__sbr_cell_5_1293:
    mov DWORD PTR [rbx+0], 1
__sbr_cell_5_1293_end:
ff_ps_read_data.L1404:
__sbr_cell_5_1294:
    sub r8d, DWORD PTR [rbp-140]
__sbr_cell_5_1294_end:
__sbr_cell_5_1295:
    cmp r8d, r15d
__sbr_cell_5_1295_end:
__sbr_cell_5_1296:
    jle ff_ps_read_data.L142f
__sbr_cell_5_1296_end:
__sbr_cell_5_1297:
    lea rdx, [rip+L_str_6]
__sbr_cell_5_1297_end:
__sbr_cell_5_1298:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_5_1298_end:
__sbr_cell_5_1299:
    mov esi, 16
__sbr_cell_5_1299_end:
__sbr_cell_5_1300:
    mov ecx, r15d
__sbr_cell_5_1300_end:
__sbr_cell_5_1301:
    xor eax, eax
__sbr_cell_5_1301_end:
__sbr_cell_5_1302:
    vzeroupper
__sbr_cell_5_1302_end:
__sbr_cell_5_1303:
    call av_log
__sbr_cell_5_1303_end:
__sbr_cell_5_1304:
    jmp ff_ps_read_data.L1479
__sbr_cell_5_1304_end:
ff_ps_read_data.L142f:
__sbr_cell_5_1305:
    mov rsi, QWORD PTR [rbp-152]
__sbr_cell_5_1305_end:
__sbr_cell_5_1306:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_5_1306_end:
__sbr_cell_5_1307:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_5_1307_end:
__sbr_cell_5_1308:
    mov edx, eax
__sbr_cell_5_1308_end:
__sbr_cell_5_1309:
    neg edx
__sbr_cell_5_1309_end:
__sbr_cell_5_1310:
    sub ecx, eax
__sbr_cell_5_1310_end:
__sbr_cell_5_1311:
    cmp r8d, ecx
__sbr_cell_5_1311_end:
__sbr_cell_5_1312:
    cmovl ecx, r8d
__sbr_cell_5_1312_end:
ff_ps_read_data.L1449:
__sbr_cell_5_1313:
    cmp r8d, edx
__sbr_cell_5_1313_end:
__sbr_cell_5_1314:
    cmovl ecx, edx
__sbr_cell_5_1314_end:
__sbr_cell_5_1315:
    add ecx, eax
__sbr_cell_5_1315_end:
__sbr_cell_5_1316:
    mov DWORD PTR [rsi+8], ecx
__sbr_cell_5_1316_end:
__sbr_cell_5_1317:
    mov r15d, r8d
__sbr_cell_5_1317_end:
__sbr_cell_5_1318:
    jmp ff_ps_read_data.L14b7
__sbr_cell_5_1318_end:
ff_ps_read_data.L1459:
__sbr_cell_5_1319:
    lea rdx, [rip+L_str_3]
__sbr_cell_5_1319_end:
__sbr_cell_5_1320:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_5_1320_end:
ff_ps_read_data.L1464:
__sbr_cell_5_1321:
    mov esi, 16
__sbr_cell_5_1321_end:
__sbr_cell_5_1322:
    mov ecx, eax
__sbr_cell_5_1322_end:
__sbr_cell_5_1323:
    xor eax, eax
__sbr_cell_5_1323_end:
__sbr_cell_5_1324:
    vzeroupper
__sbr_cell_5_1324_end:
__sbr_cell_5_1325:
    call av_log
__sbr_cell_5_1325_end:
ff_ps_read_data.L1475:
__sbr_cell_5_1326:
    mov r15d, DWORD PTR [rbp-44]
__sbr_cell_5_1326_end:
ff_ps_read_data.L1479:
__sbr_cell_5_1327:
    mov DWORD PTR [rbx+0], 0
__sbr_cell_5_1327_end:
__sbr_cell_5_1328:
    mov rsi, QWORD PTR [rbp-152]
__sbr_cell_5_1328_end:
__sbr_cell_5_1329:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_5_1329_end:
__sbr_cell_5_1330:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_5_1330_end:
__sbr_cell_5_1331:
    mov edx, eax
__sbr_cell_5_1331_end:
__sbr_cell_5_1332:
    neg edx
__sbr_cell_5_1332_end:
__sbr_cell_5_1333:
    sub ecx, eax
__sbr_cell_5_1333_end:
__sbr_cell_5_1334:
    cmp r15d, ecx
__sbr_cell_5_1334_end:
__sbr_cell_5_1335:
    cmovl ecx, r15d
__sbr_cell_5_1335_end:
ff_ps_read_data.L1499:
__sbr_cell_5_1336:
    cmp r15d, edx
__sbr_cell_5_1336_end:
__sbr_cell_5_1337:
    cmovl ecx, edx
__sbr_cell_5_1337_end:
__sbr_cell_5_1338:
    add ecx, eax
__sbr_cell_5_1338_end:
__sbr_cell_5_1339:
    mov DWORD PTR [rsi+8], ecx
__sbr_cell_5_1339_end:
__sbr_cell_5_1340:
    add rbx, 76
__sbr_cell_5_1340_end:
__sbr_cell_5_1341:
    mov edx, 680
__sbr_cell_5_1341_end:
__sbr_cell_5_1342:
    mov rdi, rbx
__sbr_cell_5_1342_end:
__sbr_cell_5_1343:
    xor esi, esi
__sbr_cell_5_1343_end:
__sbr_cell_5_1344:
    call memset
__sbr_cell_5_1344_end:
ff_ps_read_data.L14b7:
__sbr_cell_5_1345:
    mov eax, r15d
__sbr_cell_5_1345_end:
__sbr_cell_5_1346:
    add rsp, 120
__sbr_cell_5_1346_end:
__sbr_cell_5_1347:
    pop rbx
__sbr_cell_5_1347_end:
__sbr_cell_5_1348:
    pop r12
__sbr_cell_5_1348_end:
__sbr_cell_5_1349:
    pop r13
__sbr_cell_5_1349_end:
__sbr_cell_5_1350:
    pop r14
__sbr_cell_5_1350_end:
__sbr_cell_5_1351:
    pop r15
__sbr_cell_5_1351_end:
__sbr_cell_5_1352:
    pop rbp
__sbr_cell_5_1352_end:
__sbr_cell_5_1353:
    vzeroupper
__sbr_cell_5_1353_end:
ff_ps_read_data.done:
__sbr_cell_5_1354:
    ret
__sbr_cell_5_1354_end:
ff_ps_read_data.L14cc:
__sbr_cell_5_1355:
    lea rdx, [rip+L_str_4]
__sbr_cell_5_1355_end:
__sbr_cell_5_1356:
    mov rdi, QWORD PTR [rbp-64]
__sbr_cell_5_1356_end:
__sbr_cell_5_1357:
    mov esi, 16
__sbr_cell_5_1357_end:
__sbr_cell_5_1358:
    xor eax, eax
__sbr_cell_5_1358_end:
__sbr_cell_5_1359:
    vzeroupper
__sbr_cell_5_1359_end:
__sbr_cell_5_1360:
    call av_log
__sbr_cell_5_1360_end:
__sbr_cell_5_1361:
    mov rbx, QWORD PTR [rbp-56]
__sbr_cell_5_1361_end:
__sbr_cell_5_1362:
    jmp ff_ps_read_data.L1479
__sbr_cell_5_1362_end:
ff_ps_read_data.L14ec:
__sbr_cell_5_1363:
    cmp ecx, 1
__sbr_cell_5_1363_end:
__sbr_cell_5_1364:
    jne ff_ps_read_data.L14fd
__sbr_cell_5_1364_end:
ff_ps_read_data.L14f1:
__sbr_cell_5_1365:
    inc r12d
__sbr_cell_5_1365_end:
__sbr_cell_5_1366:
    mov DWORD PTR [rbx+44], r12d
__sbr_cell_5_1366_end:
__sbr_cell_5_1367:
    jmp ff_ps_read_data.L135c
__sbr_cell_5_1367_end:
ff_ps_read_data.L14fd:
__sbr_cell_5_1368:
    cmp BYTE PTR [rdx+1], 7
__sbr_cell_5_1368_end:
__sbr_cell_5_1369:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1369_end:
__sbr_cell_5_1370:
    cmp ecx, 2
__sbr_cell_5_1370_end:
__sbr_cell_5_1371:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1371_end:
__sbr_cell_5_1372:
    cmp BYTE PTR [rdx+2], 7
__sbr_cell_5_1372_end:
__sbr_cell_5_1373:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1373_end:
__sbr_cell_5_1374:
    cmp ecx, 3
__sbr_cell_5_1374_end:
__sbr_cell_5_1375:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1375_end:
__sbr_cell_5_1376:
    cmp BYTE PTR [rdx+3], 7
__sbr_cell_5_1376_end:
__sbr_cell_5_1377:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1377_end:
__sbr_cell_5_1378:
    cmp ecx, 4
__sbr_cell_5_1378_end:
__sbr_cell_5_1379:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1379_end:
ff_ps_read_data.L152a:
__sbr_cell_5_1380:
    cmp BYTE PTR [rdx+4], 7
__sbr_cell_5_1380_end:
__sbr_cell_5_1381:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1381_end:
__sbr_cell_5_1382:
    cmp ecx, 5
__sbr_cell_5_1382_end:
__sbr_cell_5_1383:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1383_end:
__sbr_cell_5_1384:
    cmp BYTE PTR [rdx+5], 7
__sbr_cell_5_1384_end:
__sbr_cell_5_1385:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1385_end:
__sbr_cell_5_1386:
    cmp ecx, 6
__sbr_cell_5_1386_end:
__sbr_cell_5_1387:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1387_end:
__sbr_cell_5_1388:
    cmp BYTE PTR [rdx+6], 7
__sbr_cell_5_1388_end:
__sbr_cell_5_1389:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1389_end:
__sbr_cell_5_1390:
    cmp ecx, 7
__sbr_cell_5_1390_end:
__sbr_cell_5_1391:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1391_end:
ff_ps_read_data.L1557:
__sbr_cell_5_1392:
    cmp BYTE PTR [rdx+7], 7
__sbr_cell_5_1392_end:
__sbr_cell_5_1393:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1393_end:
__sbr_cell_5_1394:
    cmp ecx, 8
__sbr_cell_5_1394_end:
__sbr_cell_5_1395:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1395_end:
__sbr_cell_5_1396:
    cmp BYTE PTR [rdx+8], 7
__sbr_cell_5_1396_end:
__sbr_cell_5_1397:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1397_end:
__sbr_cell_5_1398:
    cmp ecx, 9
__sbr_cell_5_1398_end:
__sbr_cell_5_1399:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1399_end:
__sbr_cell_5_1400:
    cmp BYTE PTR [rdx+9], 7
__sbr_cell_5_1400_end:
__sbr_cell_5_1401:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1401_end:
__sbr_cell_5_1402:
    cmp ecx, 10
__sbr_cell_5_1402_end:
__sbr_cell_5_1403:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1403_end:
ff_ps_read_data.L158c:
__sbr_cell_5_1404:
    cmp BYTE PTR [rdx+10], 7
__sbr_cell_5_1404_end:
__sbr_cell_5_1405:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1405_end:
__sbr_cell_5_1406:
    cmp ecx, 11
__sbr_cell_5_1406_end:
__sbr_cell_5_1407:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1407_end:
__sbr_cell_5_1408:
    cmp BYTE PTR [rdx+11], 7
__sbr_cell_5_1408_end:
__sbr_cell_5_1409:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1409_end:
__sbr_cell_5_1410:
    cmp ecx, 12
__sbr_cell_5_1410_end:
__sbr_cell_5_1411:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1411_end:
__sbr_cell_5_1412:
    cmp BYTE PTR [rdx+12], 7
__sbr_cell_5_1412_end:
__sbr_cell_5_1413:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1413_end:
__sbr_cell_5_1414:
    cmp ecx, 13
__sbr_cell_5_1414_end:
__sbr_cell_5_1415:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1415_end:
ff_ps_read_data.L15c5:
__sbr_cell_5_1416:
    cmp BYTE PTR [rdx+13], 7
__sbr_cell_5_1416_end:
__sbr_cell_5_1417:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1417_end:
__sbr_cell_5_1418:
    cmp ecx, 14
__sbr_cell_5_1418_end:
__sbr_cell_5_1419:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1419_end:
__sbr_cell_5_1420:
    cmp BYTE PTR [rdx+14], 7
__sbr_cell_5_1420_end:
__sbr_cell_5_1421:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1421_end:
__sbr_cell_5_1422:
    cmp ecx, 15
__sbr_cell_5_1422_end:
__sbr_cell_5_1423:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1423_end:
__sbr_cell_5_1424:
    cmp BYTE PTR [rdx+15], 7
__sbr_cell_5_1424_end:
__sbr_cell_5_1425:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1425_end:
__sbr_cell_5_1426:
    cmp ecx, 16
__sbr_cell_5_1426_end:
__sbr_cell_5_1427:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1427_end:
ff_ps_read_data.L15fe:
__sbr_cell_5_1428:
    cmp BYTE PTR [rdx+16], 7
__sbr_cell_5_1428_end:
__sbr_cell_5_1429:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1429_end:
__sbr_cell_5_1430:
    cmp ecx, 17
__sbr_cell_5_1430_end:
__sbr_cell_5_1431:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1431_end:
__sbr_cell_5_1432:
    cmp BYTE PTR [rdx+17], 7
__sbr_cell_5_1432_end:
__sbr_cell_5_1433:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1433_end:
__sbr_cell_5_1434:
    cmp ecx, 18
__sbr_cell_5_1434_end:
__sbr_cell_5_1435:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1435_end:
__sbr_cell_5_1436:
    cmp BYTE PTR [rdx+18], 7
__sbr_cell_5_1436_end:
__sbr_cell_5_1437:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1437_end:
__sbr_cell_5_1438:
    cmp ecx, 19
__sbr_cell_5_1438_end:
__sbr_cell_5_1439:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1439_end:
ff_ps_read_data.L1637:
__sbr_cell_5_1440:
    cmp BYTE PTR [rdx+19], 7
__sbr_cell_5_1440_end:
__sbr_cell_5_1441:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1441_end:
__sbr_cell_5_1442:
    cmp ecx, 20
__sbr_cell_5_1442_end:
__sbr_cell_5_1443:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1443_end:
__sbr_cell_5_1444:
    cmp BYTE PTR [rdx+20], 7
__sbr_cell_5_1444_end:
__sbr_cell_5_1445:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1445_end:
__sbr_cell_5_1446:
    cmp ecx, 21
__sbr_cell_5_1446_end:
__sbr_cell_5_1447:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1447_end:
__sbr_cell_5_1448:
    cmp BYTE PTR [rdx+21], 7
__sbr_cell_5_1448_end:
__sbr_cell_5_1449:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1449_end:
__sbr_cell_5_1450:
    cmp ecx, 22
__sbr_cell_5_1450_end:
__sbr_cell_5_1451:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1451_end:
ff_ps_read_data.L1670:
__sbr_cell_5_1452:
    cmp BYTE PTR [rdx+22], 7
__sbr_cell_5_1452_end:
__sbr_cell_5_1453:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1453_end:
__sbr_cell_5_1454:
    cmp ecx, 23
__sbr_cell_5_1454_end:
__sbr_cell_5_1455:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1455_end:
__sbr_cell_5_1456:
    cmp BYTE PTR [rdx+23], 7
__sbr_cell_5_1456_end:
__sbr_cell_5_1457:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1457_end:
__sbr_cell_5_1458:
    cmp ecx, 24
__sbr_cell_5_1458_end:
__sbr_cell_5_1459:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1459_end:
__sbr_cell_5_1460:
    cmp BYTE PTR [rdx+24], 7
__sbr_cell_5_1460_end:
__sbr_cell_5_1461:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1461_end:
__sbr_cell_5_1462:
    cmp ecx, 25
__sbr_cell_5_1462_end:
__sbr_cell_5_1463:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1463_end:
ff_ps_read_data.L16a9:
__sbr_cell_5_1464:
    cmp BYTE PTR [rdx+25], 7
__sbr_cell_5_1464_end:
__sbr_cell_5_1465:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1465_end:
__sbr_cell_5_1466:
    cmp ecx, 26
__sbr_cell_5_1466_end:
__sbr_cell_5_1467:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1467_end:
__sbr_cell_5_1468:
    cmp BYTE PTR [rdx+26], 7
__sbr_cell_5_1468_end:
__sbr_cell_5_1469:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1469_end:
__sbr_cell_5_1470:
    cmp ecx, 27
__sbr_cell_5_1470_end:
__sbr_cell_5_1471:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1471_end:
__sbr_cell_5_1472:
    cmp BYTE PTR [rdx+27], 7
__sbr_cell_5_1472_end:
__sbr_cell_5_1473:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1473_end:
__sbr_cell_5_1474:
    cmp ecx, 28
__sbr_cell_5_1474_end:
__sbr_cell_5_1475:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1475_end:
ff_ps_read_data.L16e2:
__sbr_cell_5_1476:
    cmp BYTE PTR [rdx+28], 7
__sbr_cell_5_1476_end:
__sbr_cell_5_1477:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1477_end:
__sbr_cell_5_1478:
    cmp ecx, 29
__sbr_cell_5_1478_end:
__sbr_cell_5_1479:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1479_end:
__sbr_cell_5_1480:
    cmp BYTE PTR [rdx+29], 7
__sbr_cell_5_1480_end:
__sbr_cell_5_1481:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1481_end:
__sbr_cell_5_1482:
    cmp ecx, 30
__sbr_cell_5_1482_end:
__sbr_cell_5_1483:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1483_end:
__sbr_cell_5_1484:
    cmp BYTE PTR [rdx+30], 7
__sbr_cell_5_1484_end:
__sbr_cell_5_1485:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1485_end:
__sbr_cell_5_1486:
    cmp ecx, 31
__sbr_cell_5_1486_end:
__sbr_cell_5_1487:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1487_end:
ff_ps_read_data.L171b:
__sbr_cell_5_1488:
    cmp BYTE PTR [rdx+31], 7
__sbr_cell_5_1488_end:
__sbr_cell_5_1489:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1489_end:
__sbr_cell_5_1490:
    cmp ecx, 32
__sbr_cell_5_1490_end:
__sbr_cell_5_1491:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1491_end:
__sbr_cell_5_1492:
    cmp BYTE PTR [rdx+32], 7
__sbr_cell_5_1492_end:
__sbr_cell_5_1493:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1493_end:
__sbr_cell_5_1494:
    cmp ecx, 33
__sbr_cell_5_1494_end:
__sbr_cell_5_1495:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1495_end:
__sbr_cell_5_1496:
    cmp BYTE PTR [rdx+33], 7
__sbr_cell_5_1496_end:
__sbr_cell_5_1497:
    ja ff_ps_read_data.L132a
__sbr_cell_5_1497_end:
__sbr_cell_5_1498:
    cmp ecx, 34
__sbr_cell_5_1498_end:
__sbr_cell_5_1499:
    je ff_ps_read_data.L14f1
__sbr_cell_5_1499_end:
__sbr_cell_5_1500:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1500_end:
ff_ps_read_data.L1759:
__sbr_cell_5_1501:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1501_end:
ff_ps_read_data.L175e:
__sbr_cell_5_1502:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1502_end:
ff_ps_read_data.L1763:
__sbr_cell_5_1503:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1503_end:
ff_ps_read_data.L1768:
__sbr_cell_5_1504:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1504_end:
ff_ps_read_data.L176d:
__sbr_cell_5_1505:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1505_end:
ff_ps_read_data.L1772:
__sbr_cell_5_1506:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1506_end:
ff_ps_read_data.L1777:
__sbr_cell_5_1507:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1507_end:
ff_ps_read_data.L177c:
__sbr_cell_5_1508:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1508_end:
ff_ps_read_data.L1781:
__sbr_cell_5_1509:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1509_end:
ff_ps_read_data.L1786:
__sbr_cell_5_1510:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1510_end:
ff_ps_read_data.L178b:
__sbr_cell_5_1511:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1511_end:
ff_ps_read_data.L1790:
__sbr_cell_5_1512:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1512_end:
ff_ps_read_data.L1795:
__sbr_cell_5_1513:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1513_end:
ff_ps_read_data.L179a:
__sbr_cell_5_1514:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1514_end:
ff_ps_read_data.L179f:
__sbr_cell_5_1515:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1515_end:
ff_ps_read_data.L17a4:
__sbr_cell_5_1516:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1516_end:
ff_ps_read_data.L17a9:
__sbr_cell_5_1517:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1517_end:
ff_ps_read_data.L17ae:
__sbr_cell_5_1518:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1518_end:
ff_ps_read_data.L17b3:
__sbr_cell_5_1519:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1519_end:
ff_ps_read_data.L17b8:
__sbr_cell_5_1520:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1520_end:
ff_ps_read_data.L17bd:
__sbr_cell_5_1521:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1521_end:
ff_ps_read_data.L17c2:
__sbr_cell_5_1522:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1522_end:
ff_ps_read_data.L17c7:
__sbr_cell_5_1523:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1523_end:
ff_ps_read_data.L17cc:
__sbr_cell_5_1524:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1524_end:
ff_ps_read_data.L17d1:
__sbr_cell_5_1525:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_5_1525_end:
.size ff_ps_read_data, .-ff_ps_read_data
.section .text.ff_sbr_autocorrelate_sse,"ax",@progbits
.globl ff_sbr_autocorrelate_sse
.type ff_sbr_autocorrelate_sse,@function
ff_sbr_autocorrelate_sse:
__sbr_cell_6_0:
    sub rsp, 40
__sbr_cell_6_0_end:
__sbr_cell_6_1:
    mov edx, 296
__sbr_cell_6_1_end:
__sbr_cell_6_2:
    add rdi, rdx
__sbr_cell_6_2_end:
__sbr_cell_6_3:
    neg rdx
__sbr_cell_6_3_end:
__sbr_cell_6_4:
    movlps xmm5, QWORD PTR [rdi+rdx*1+0]
__sbr_cell_6_4_end:
__sbr_cell_6_5:
    movlhps xmm5, xmm5
__sbr_cell_6_5_end:
__sbr_cell_6_6:
    movlps xmm7, QWORD PTR [rdi+rdx*1+8]
__sbr_cell_6_6_end:
__sbr_cell_6_7:
    movlps xmm1, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_6_7_end:
__sbr_cell_6_8:
    shufps xmm7, xmm7, 20
__sbr_cell_6_8_end:
__sbr_cell_6_9:
    shufps xmm1, xmm1, 20
__sbr_cell_6_9_end:
__sbr_cell_6_10:
    movaps xmm3, xmm5
__sbr_cell_6_10_end:
__sbr_cell_6_11:
    mulps xmm3, xmm7
__sbr_cell_6_11_end:
__sbr_cell_6_12:
    movaps xmm4, xmm5
__sbr_cell_6_12_end:
__sbr_cell_6_13:
    mulps xmm4, xmm5
__sbr_cell_6_13_end:
__sbr_cell_6_14:
    mulps xmm5, xmm1
__sbr_cell_6_14_end:
__sbr_cell_6_15:
    movaps XMMWORD PTR [rsp+0], xmm3
__sbr_cell_6_15_end:
__sbr_cell_6_16:
    movaps XMMWORD PTR [rsp+16], xmm4
__sbr_cell_6_16_end:
__sbr_cell_6_17:
    add rdx, 8
__sbr_cell_6_17_end:
__sbr_cell_6_18:
    movlps xmm2, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_6_18_end:
__sbr_cell_6_19:
    movlhps xmm7, xmm7
__sbr_cell_6_19_end:
__sbr_cell_6_20:
    shufps xmm2, xmm2, 20
__sbr_cell_6_20_end:
__sbr_cell_6_21:
    movaps xmm6, xmm7
__sbr_cell_6_21_end:
__sbr_cell_6_22:
    mulps xmm6, xmm1
__sbr_cell_6_22_end:
__sbr_cell_6_23:
    movaps xmm4, xmm7
__sbr_cell_6_23_end:
__sbr_cell_6_24:
    mulps xmm4, xmm2
__sbr_cell_6_24_end:
__sbr_cell_6_25:
    mulps xmm7, xmm7
__sbr_cell_6_25_end:
__sbr_cell_6_26:
    addps xmm5, xmm4
__sbr_cell_6_26_end:
__sbr_cell_6_27:
    .nops 1
__sbr_cell_6_27_end:
__sbr_cell_6_28:
    .nops 1
__sbr_cell_6_28_end:
ff_sbr_autocorrelate_sse.loop:
__sbr_cell_6_29:
    add rdx, 8
__sbr_cell_6_29_end:
__sbr_cell_6_30:
    movlps xmm0, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_6_30_end:
__sbr_cell_6_31:
    movlhps xmm1, xmm1
__sbr_cell_6_31_end:
__sbr_cell_6_32:
    shufps xmm0, xmm0, 20
__sbr_cell_6_32_end:
__sbr_cell_6_33:
    movaps xmm3, xmm1
__sbr_cell_6_33_end:
__sbr_cell_6_34:
    mulps xmm3, xmm2
__sbr_cell_6_34_end:
__sbr_cell_6_35:
    movaps xmm4, xmm1
__sbr_cell_6_35_end:
__sbr_cell_6_36:
    mulps xmm4, xmm0
__sbr_cell_6_36_end:
__sbr_cell_6_37:
    mulps xmm1, xmm1
__sbr_cell_6_37_end:
__sbr_cell_6_38:
    addps xmm6, xmm3
__sbr_cell_6_38_end:
__sbr_cell_6_39:
    addps xmm5, xmm4
__sbr_cell_6_39_end:
__sbr_cell_6_40:
    addps xmm7, xmm1
__sbr_cell_6_40_end:
__sbr_cell_6_41:
    add rdx, 8
__sbr_cell_6_41_end:
__sbr_cell_6_42:
    movlps xmm1, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_6_42_end:
__sbr_cell_6_43:
    movlhps xmm2, xmm2
__sbr_cell_6_43_end:
__sbr_cell_6_44:
    shufps xmm1, xmm1, 20
__sbr_cell_6_44_end:
__sbr_cell_6_45:
    movaps xmm3, xmm2
__sbr_cell_6_45_end:
__sbr_cell_6_46:
    mulps xmm3, xmm0
__sbr_cell_6_46_end:
__sbr_cell_6_47:
    movaps xmm4, xmm2
__sbr_cell_6_47_end:
__sbr_cell_6_48:
    mulps xmm4, xmm1
__sbr_cell_6_48_end:
__sbr_cell_6_49:
    mulps xmm2, xmm2
__sbr_cell_6_49_end:
__sbr_cell_6_50:
    addps xmm6, xmm3
__sbr_cell_6_50_end:
__sbr_cell_6_51:
    addps xmm5, xmm4
__sbr_cell_6_51_end:
__sbr_cell_6_52:
    addps xmm7, xmm2
__sbr_cell_6_52_end:
__sbr_cell_6_53:
    add rdx, 8
__sbr_cell_6_53_end:
__sbr_cell_6_54:
    movlps xmm2, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_6_54_end:
__sbr_cell_6_55:
    movlhps xmm0, xmm0
__sbr_cell_6_55_end:
__sbr_cell_6_56:
    shufps xmm2, xmm2, 20
__sbr_cell_6_56_end:
__sbr_cell_6_57:
    movaps xmm3, xmm0
__sbr_cell_6_57_end:
__sbr_cell_6_58:
    mulps xmm3, xmm1
__sbr_cell_6_58_end:
__sbr_cell_6_59:
    movaps xmm4, xmm0
__sbr_cell_6_59_end:
__sbr_cell_6_60:
    mulps xmm4, xmm2
__sbr_cell_6_60_end:
__sbr_cell_6_61:
    mulps xmm0, xmm0
__sbr_cell_6_61_end:
__sbr_cell_6_62:
    addps xmm6, xmm3
__sbr_cell_6_62_end:
__sbr_cell_6_63:
    addps xmm5, xmm4
__sbr_cell_6_63_end:
__sbr_cell_6_64:
    addps xmm7, xmm0
__sbr_cell_6_64_end:
__sbr_cell_6_65:
    jl ff_sbr_autocorrelate_sse.loop
__sbr_cell_6_65_end:
ff_sbr_autocorrelate_sse.tail:
__sbr_cell_6_66:
    movlhps xmm1, xmm1
__sbr_cell_6_66_end:
__sbr_cell_6_67:
    mulps xmm2, xmm1
__sbr_cell_6_67_end:
__sbr_cell_6_68:
    mulps xmm1, xmm1
__sbr_cell_6_68_end:
__sbr_cell_6_69:
    addps xmm2, xmm6
__sbr_cell_6_69_end:
__sbr_cell_6_70:
    addps xmm1, xmm7
__sbr_cell_6_70_end:
__sbr_cell_6_71:
    addps xmm6, XMMWORD PTR [rsp+0]
__sbr_cell_6_71_end:
__sbr_cell_6_72:
    addps xmm7, XMMWORD PTR [rsp+16]
__sbr_cell_6_72_end:
__sbr_cell_6_73:
    xorps xmm2, XMMWORD PTR [rip+ps_mask3]
__sbr_cell_6_73_end:
__sbr_cell_6_74:
    xorps xmm5, XMMWORD PTR [rip+ps_mask3]
__sbr_cell_6_74_end:
__sbr_cell_6_75:
    xorps xmm6, XMMWORD PTR [rip+ps_mask3]
__sbr_cell_6_75_end:
__sbr_cell_6_76:
    movaps xmm3, xmm2
__sbr_cell_6_76_end:
__sbr_cell_6_77:
    shufps xmm2, xmm5, 136
__sbr_cell_6_77_end:
__sbr_cell_6_78:
    shufps xmm3, xmm5, 221
__sbr_cell_6_78_end:
__sbr_cell_6_79:
    addps xmm2, xmm3
__sbr_cell_6_79_end:
__sbr_cell_6_80:
    movaps xmm4, xmm7
__sbr_cell_6_80_end:
__sbr_cell_6_81:
    shufps xmm7, xmm6, 136
__sbr_cell_6_81_end:
__sbr_cell_6_82:
    shufps xmm4, xmm6, 221
__sbr_cell_6_82_end:
__sbr_cell_6_83:
    addps xmm7, xmm4
__sbr_cell_6_83_end:
__sbr_cell_6_84:
    movss xmm0, xmm1
__sbr_cell_6_84_end:
__sbr_cell_6_85:
    shufps xmm1, xmm1, 1
__sbr_cell_6_85_end:
__sbr_cell_6_86:
    addss xmm1, xmm0
__sbr_cell_6_86_end:
__sbr_cell_6_87:
    movaps XMMWORD PTR [rsi+0], xmm2
__sbr_cell_6_87_end:
__sbr_cell_6_88:
    movhps QWORD PTR [rsi+24], xmm7
__sbr_cell_6_88_end:
__sbr_cell_6_89:
    movss DWORD PTR [rsi+40], xmm7
__sbr_cell_6_89_end:
__sbr_cell_6_90:
    movss DWORD PTR [rsi+16], xmm1
__sbr_cell_6_90_end:
__sbr_cell_6_91:
    add rsp, 40
__sbr_cell_6_91_end:
ff_sbr_autocorrelate_sse.done:
__sbr_cell_6_92:
    ret
__sbr_cell_6_92_end:
.size ff_sbr_autocorrelate_sse, .-ff_sbr_autocorrelate_sse
.section .text.ff_sbr_autocorrelate_sse3,"ax",@progbits
.globl ff_sbr_autocorrelate_sse3
.type ff_sbr_autocorrelate_sse3,@function
ff_sbr_autocorrelate_sse3:
__sbr_cell_7_0:
    sub rsp, 40
__sbr_cell_7_0_end:
__sbr_cell_7_1:
    mov edx, 296
__sbr_cell_7_1_end:
__sbr_cell_7_2:
    add rdi, rdx
__sbr_cell_7_2_end:
__sbr_cell_7_3:
    neg rdx
__sbr_cell_7_3_end:
__sbr_cell_7_4:
    movddup xmm5, QWORD PTR [rdi+rdx*1+0]
__sbr_cell_7_4_end:
__sbr_cell_7_5:
    movsd xmm7, QWORD PTR [rdi+rdx*1+8]
__sbr_cell_7_5_end:
__sbr_cell_7_6:
    movsd xmm1, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_7_6_end:
__sbr_cell_7_7:
    shufps xmm7, xmm7, 20
__sbr_cell_7_7_end:
__sbr_cell_7_8:
    shufps xmm1, xmm1, 20
__sbr_cell_7_8_end:
__sbr_cell_7_9:
    movaps xmm3, xmm5
__sbr_cell_7_9_end:
__sbr_cell_7_10:
    mulps xmm3, xmm7
__sbr_cell_7_10_end:
__sbr_cell_7_11:
    movaps xmm4, xmm5
__sbr_cell_7_11_end:
__sbr_cell_7_12:
    mulps xmm4, xmm5
__sbr_cell_7_12_end:
__sbr_cell_7_13:
    mulps xmm5, xmm1
__sbr_cell_7_13_end:
__sbr_cell_7_14:
    movaps XMMWORD PTR [rsp+0], xmm3
__sbr_cell_7_14_end:
__sbr_cell_7_15:
    movaps XMMWORD PTR [rsp+16], xmm4
__sbr_cell_7_15_end:
__sbr_cell_7_16:
    add rdx, 8
__sbr_cell_7_16_end:
__sbr_cell_7_17:
    movsd xmm2, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_7_17_end:
__sbr_cell_7_18:
    movlhps xmm7, xmm7
__sbr_cell_7_18_end:
__sbr_cell_7_19:
    shufps xmm2, xmm2, 20
__sbr_cell_7_19_end:
__sbr_cell_7_20:
    movaps xmm6, xmm7
__sbr_cell_7_20_end:
__sbr_cell_7_21:
    mulps xmm6, xmm1
__sbr_cell_7_21_end:
__sbr_cell_7_22:
    movaps xmm4, xmm7
__sbr_cell_7_22_end:
__sbr_cell_7_23:
    mulps xmm4, xmm2
__sbr_cell_7_23_end:
__sbr_cell_7_24:
    mulps xmm7, xmm7
__sbr_cell_7_24_end:
__sbr_cell_7_25:
    addps xmm5, xmm4
__sbr_cell_7_25_end:
__sbr_cell_7_26:
    .nops 1
__sbr_cell_7_26_end:
__sbr_cell_7_27:
    .nops 1
__sbr_cell_7_27_end:
ff_sbr_autocorrelate_sse3.loop:
__sbr_cell_7_28:
    add rdx, 8
__sbr_cell_7_28_end:
__sbr_cell_7_29:
    movsd xmm0, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_7_29_end:
__sbr_cell_7_30:
    movlhps xmm1, xmm1
__sbr_cell_7_30_end:
__sbr_cell_7_31:
    shufps xmm0, xmm0, 20
__sbr_cell_7_31_end:
__sbr_cell_7_32:
    movaps xmm3, xmm1
__sbr_cell_7_32_end:
__sbr_cell_7_33:
    mulps xmm3, xmm2
__sbr_cell_7_33_end:
__sbr_cell_7_34:
    movaps xmm4, xmm1
__sbr_cell_7_34_end:
__sbr_cell_7_35:
    mulps xmm4, xmm0
__sbr_cell_7_35_end:
__sbr_cell_7_36:
    mulps xmm1, xmm1
__sbr_cell_7_36_end:
__sbr_cell_7_37:
    addps xmm6, xmm3
__sbr_cell_7_37_end:
__sbr_cell_7_38:
    addps xmm5, xmm4
__sbr_cell_7_38_end:
__sbr_cell_7_39:
    addps xmm7, xmm1
__sbr_cell_7_39_end:
__sbr_cell_7_40:
    add rdx, 8
__sbr_cell_7_40_end:
__sbr_cell_7_41:
    movsd xmm1, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_7_41_end:
__sbr_cell_7_42:
    movlhps xmm2, xmm2
__sbr_cell_7_42_end:
__sbr_cell_7_43:
    shufps xmm1, xmm1, 20
__sbr_cell_7_43_end:
__sbr_cell_7_44:
    movaps xmm3, xmm2
__sbr_cell_7_44_end:
__sbr_cell_7_45:
    mulps xmm3, xmm0
__sbr_cell_7_45_end:
__sbr_cell_7_46:
    movaps xmm4, xmm2
__sbr_cell_7_46_end:
__sbr_cell_7_47:
    mulps xmm4, xmm1
__sbr_cell_7_47_end:
__sbr_cell_7_48:
    mulps xmm2, xmm2
__sbr_cell_7_48_end:
__sbr_cell_7_49:
    addps xmm6, xmm3
__sbr_cell_7_49_end:
__sbr_cell_7_50:
    addps xmm5, xmm4
__sbr_cell_7_50_end:
__sbr_cell_7_51:
    addps xmm7, xmm2
__sbr_cell_7_51_end:
__sbr_cell_7_52:
    add rdx, 8
__sbr_cell_7_52_end:
__sbr_cell_7_53:
    movsd xmm2, QWORD PTR [rdi+rdx*1+16]
__sbr_cell_7_53_end:
__sbr_cell_7_54:
    movlhps xmm0, xmm0
__sbr_cell_7_54_end:
__sbr_cell_7_55:
    shufps xmm2, xmm2, 20
__sbr_cell_7_55_end:
__sbr_cell_7_56:
    movaps xmm3, xmm0
__sbr_cell_7_56_end:
__sbr_cell_7_57:
    mulps xmm3, xmm1
__sbr_cell_7_57_end:
__sbr_cell_7_58:
    movaps xmm4, xmm0
__sbr_cell_7_58_end:
__sbr_cell_7_59:
    mulps xmm4, xmm2
__sbr_cell_7_59_end:
__sbr_cell_7_60:
    mulps xmm0, xmm0
__sbr_cell_7_60_end:
__sbr_cell_7_61:
    addps xmm6, xmm3
__sbr_cell_7_61_end:
__sbr_cell_7_62:
    addps xmm5, xmm4
__sbr_cell_7_62_end:
__sbr_cell_7_63:
    addps xmm7, xmm0
__sbr_cell_7_63_end:
__sbr_cell_7_64:
    jl ff_sbr_autocorrelate_sse3.loop
__sbr_cell_7_64_end:
ff_sbr_autocorrelate_sse3.tail:
__sbr_cell_7_65:
    movlhps xmm1, xmm1
__sbr_cell_7_65_end:
__sbr_cell_7_66:
    mulps xmm2, xmm1
__sbr_cell_7_66_end:
__sbr_cell_7_67:
    mulps xmm1, xmm1
__sbr_cell_7_67_end:
__sbr_cell_7_68:
    addps xmm2, xmm6
__sbr_cell_7_68_end:
__sbr_cell_7_69:
    addps xmm1, xmm7
__sbr_cell_7_69_end:
__sbr_cell_7_70:
    addps xmm6, XMMWORD PTR [rsp+0]
__sbr_cell_7_70_end:
__sbr_cell_7_71:
    addps xmm7, XMMWORD PTR [rsp+16]
__sbr_cell_7_71_end:
__sbr_cell_7_72:
    xorps xmm2, XMMWORD PTR [rip+ps_mask3]
__sbr_cell_7_72_end:
__sbr_cell_7_73:
    xorps xmm5, XMMWORD PTR [rip+ps_mask3]
__sbr_cell_7_73_end:
__sbr_cell_7_74:
    xorps xmm6, XMMWORD PTR [rip+ps_mask3]
__sbr_cell_7_74_end:
__sbr_cell_7_75:
    haddps xmm2, xmm5
__sbr_cell_7_75_end:
__sbr_cell_7_76:
    haddps xmm7, xmm6
__sbr_cell_7_76_end:
__sbr_cell_7_77:
    movshdup xmm0, xmm1
__sbr_cell_7_77_end:
__sbr_cell_7_78:
    addss xmm1, xmm0
__sbr_cell_7_78_end:
__sbr_cell_7_79:
    movaps XMMWORD PTR [rsi+0], xmm2
__sbr_cell_7_79_end:
__sbr_cell_7_80:
    movhps QWORD PTR [rsi+24], xmm7
__sbr_cell_7_80_end:
__sbr_cell_7_81:
    movss DWORD PTR [rsi+40], xmm7
__sbr_cell_7_81_end:
__sbr_cell_7_82:
    movss DWORD PTR [rsi+16], xmm1
__sbr_cell_7_82_end:
__sbr_cell_7_83:
    add rsp, 40
__sbr_cell_7_83_end:
ff_sbr_autocorrelate_sse3.done:
__sbr_cell_7_84:
    ret
__sbr_cell_7_84_end:
.size ff_sbr_autocorrelate_sse3, .-ff_sbr_autocorrelate_sse3
.section .text.ff_sbr_hf_apply_noise,"ax",@progbits
.globl ff_sbr_hf_apply_noise_0_sse2
.type ff_sbr_hf_apply_noise_0_sse2,@function
ff_sbr_hf_apply_noise_0_sse2:
__sbr_cell_8_0:
    movdqa xmm0, XMMWORD PTR [rip+ps_noise0]
__sbr_cell_8_0_end:
__sbr_cell_8_1:
    jmp apply_noise_main
__sbr_cell_8_1_end:
__sbr_cell_8_2:
    .nops 6
__sbr_cell_8_2_end:
ff_sbr_hf_apply_noise_1_sse2:
__sbr_cell_8_3:
    and r8, 1
__sbr_cell_8_3_end:
__sbr_cell_8_4:
    shl r8, 4
__sbr_cell_8_4_end:
__sbr_cell_8_5:
    lea rax, [rip+ps_noise13]
__sbr_cell_8_5_end:
__sbr_cell_8_6:
    movdqa xmm0, XMMWORD PTR [r8+rax*1+0]
__sbr_cell_8_6_end:
__sbr_cell_8_7:
    jmp apply_noise_main
__sbr_cell_8_7_end:
__sbr_cell_8_8:
    .nops 8
__sbr_cell_8_8_end:
__sbr_cell_8_9:
    .nops 1
__sbr_cell_8_9_end:
ff_sbr_hf_apply_noise_2_sse2:
__sbr_cell_8_10:
    movdqa xmm0, XMMWORD PTR [rip+ps_noise2]
__sbr_cell_8_10_end:
__sbr_cell_8_11:
    jmp apply_noise_main
__sbr_cell_8_11_end:
__sbr_cell_8_12:
    .nops 6
__sbr_cell_8_12_end:
ff_sbr_hf_apply_noise_3_sse2:
__sbr_cell_8_13:
    and r8, 1
__sbr_cell_8_13_end:
__sbr_cell_8_14:
    shl r8, 4
__sbr_cell_8_14_end:
__sbr_cell_8_15:
    lea rax, [rip+(ps_noise13 + 16)]
__sbr_cell_8_15_end:
__sbr_cell_8_16:
    movdqa xmm0, XMMWORD PTR [r8+rax*1+0]
__sbr_cell_8_16_end:
apply_noise_main:
__sbr_cell_8_17:
    movsxd rcx, ecx
__sbr_cell_8_17_end:
__sbr_cell_8_18:
    dec rcx
__sbr_cell_8_18_end:
__sbr_cell_8_19:
    shl r9d, 2
__sbr_cell_8_19_end:
__sbr_cell_8_20:
    lea rax, [rip+ff_sbr_noise_table]
__sbr_cell_8_20_end:
__sbr_cell_8_21:
    lea rdi, [rdi+r9*2+0]
__sbr_cell_8_21_end:
__sbr_cell_8_22:
    add rsi, r9
__sbr_cell_8_22_end:
__sbr_cell_8_23:
    add rdx, r9
__sbr_cell_8_23_end:
__sbr_cell_8_24:
    shl rcx, 3
__sbr_cell_8_24_end:
__sbr_cell_8_25:
    pxor xmm5, xmm5
__sbr_cell_8_25_end:
__sbr_cell_8_26:
    neg r9
__sbr_cell_8_26_end:
apply_noise_main.loop:
__sbr_cell_8_27:
    movdqa xmm1, XMMWORD PTR [rdx+r9*1+0]
__sbr_cell_8_27_end:
__sbr_cell_8_28:
    movdqu xmm3, XMMWORD PTR [rcx+rax*1+16]
__sbr_cell_8_28_end:
__sbr_cell_8_29:
    movdqu xmm4, XMMWORD PTR [rcx+rax*1+32]
__sbr_cell_8_29_end:
__sbr_cell_8_30:
    add rcx, 32
__sbr_cell_8_30_end:
__sbr_cell_8_31:
    and rcx, 4088
__sbr_cell_8_31_end:
apply_noise_main.b:
__sbr_cell_8_32:
    movdqa xmm2, xmm1
__sbr_cell_8_32_end:
__sbr_cell_8_33:
    punpckhdq xmm2, xmm1
__sbr_cell_8_33_end:
__sbr_cell_8_34:
    punpckldq xmm1, xmm1
__sbr_cell_8_34_end:
__sbr_cell_8_35:
    mulps xmm1, xmm3
__sbr_cell_8_35_end:
__sbr_cell_8_36:
    mulps xmm2, xmm4
__sbr_cell_8_36_end:
__sbr_cell_8_37:
    movdqa xmm3, XMMWORD PTR [rsi+r9*1+0]
__sbr_cell_8_37_end:
__sbr_cell_8_38:
    movdqa xmm4, xmm3
__sbr_cell_8_38_end:
__sbr_cell_8_39:
    punpckhdq xmm4, xmm3
__sbr_cell_8_39_end:
__sbr_cell_8_40:
    punpckldq xmm3, xmm3
__sbr_cell_8_40_end:
__sbr_cell_8_41:
    movdqa xmm6, xmm3
__sbr_cell_8_41_end:
__sbr_cell_8_42:
    pcmpeqd xmm6, xmm5
__sbr_cell_8_42_end:
__sbr_cell_8_43:
    movdqa xmm7, xmm4
__sbr_cell_8_43_end:
__sbr_cell_8_44:
    pcmpeqd xmm7, xmm5
__sbr_cell_8_44_end:
__sbr_cell_8_45:
    mulps xmm3, xmm0
__sbr_cell_8_45_end:
__sbr_cell_8_46:
    mulps xmm4, xmm0
__sbr_cell_8_46_end:
__sbr_cell_8_47:
    pand xmm1, xmm6
__sbr_cell_8_47_end:
__sbr_cell_8_48:
    pand xmm2, xmm7
__sbr_cell_8_48_end:
apply_noise_main.c:
__sbr_cell_8_49:
    movdqu xmm6, XMMWORD PTR [rdi+r9*2+0]
__sbr_cell_8_49_end:
__sbr_cell_8_50:
    movdqu xmm7, XMMWORD PTR [rdi+r9*2+16]
__sbr_cell_8_50_end:
__sbr_cell_8_51:
    addps xmm3, xmm1
__sbr_cell_8_51_end:
__sbr_cell_8_52:
    addps xmm4, xmm2
__sbr_cell_8_52_end:
__sbr_cell_8_53:
    addps xmm6, xmm3
__sbr_cell_8_53_end:
__sbr_cell_8_54:
    addps xmm7, xmm4
__sbr_cell_8_54_end:
__sbr_cell_8_55:
    movdqu XMMWORD PTR [rdi+r9*2+0], xmm6
__sbr_cell_8_55_end:
__sbr_cell_8_56:
    movdqu XMMWORD PTR [rdi+r9*2+16], xmm7
__sbr_cell_8_56_end:
apply_noise_main.d:
__sbr_cell_8_57:
    add r9, 16
__sbr_cell_8_57_end:
__sbr_cell_8_58:
    jl apply_noise_main.loop
__sbr_cell_8_58_end:
apply_noise_main.done:
__sbr_cell_8_59:
    ret
__sbr_cell_8_59_end:
.size ff_sbr_hf_apply_noise_0_sse2, .-ff_sbr_hf_apply_noise_0_sse2
.section .text.ff_sbr_hf_g_filt_sse,"ax",@progbits
.globl ff_sbr_hf_g_filt_sse
.type ff_sbr_hf_g_filt_sse,@function
ff_sbr_hf_g_filt_sse:
__sbr_cell_9_0:
    lea rsi, [rsi+r8*8+0]
__sbr_cell_9_0_end:
__sbr_cell_9_1:
    mov r9, rcx
__sbr_cell_9_1_end:
__sbr_cell_9_2:
    and rcx, 252
__sbr_cell_9_2_end:
__sbr_cell_9_3:
    lea rdx, [rdx+rcx*4+0]
__sbr_cell_9_3_end:
__sbr_cell_9_4:
    lea rdi, [rdi+rcx*8+0]
__sbr_cell_9_4_end:
__sbr_cell_9_5:
    neg rcx
__sbr_cell_9_5_end:
__sbr_cell_9_6:
    je ff_sbr_hf_g_filt_sse.loop1
__sbr_cell_9_6_end:
ff_sbr_hf_g_filt_sse.loop4:
__sbr_cell_9_7:
    movlps xmm0, QWORD PTR [rdx+rcx*4+0]
__sbr_cell_9_7_end:
__sbr_cell_9_8:
    movlps xmm1, QWORD PTR [rdx+rcx*4+8]
__sbr_cell_9_8_end:
__sbr_cell_9_9:
    movlps xmm2, QWORD PTR [rsi+0]
__sbr_cell_9_9_end:
__sbr_cell_9_10:
    movlps xmm3, QWORD PTR [rsi+640]
__sbr_cell_9_10_end:
__sbr_cell_9_11:
    movhps xmm2, QWORD PTR [rsi+320]
__sbr_cell_9_11_end:
__sbr_cell_9_12:
    movhps xmm3, QWORD PTR [rsi+960]
__sbr_cell_9_12_end:
__sbr_cell_9_13:
    unpcklps xmm0, xmm0
__sbr_cell_9_13_end:
__sbr_cell_9_14:
    unpcklps xmm1, xmm1
__sbr_cell_9_14_end:
__sbr_cell_9_15:
    mulps xmm0, xmm2
__sbr_cell_9_15_end:
__sbr_cell_9_16:
    mulps xmm1, xmm3
__sbr_cell_9_16_end:
__sbr_cell_9_17:
    movups XMMWORD PTR [rdi+rcx*8+0], xmm0
__sbr_cell_9_17_end:
__sbr_cell_9_18:
    movups XMMWORD PTR [rdi+rcx*8+16], xmm1
__sbr_cell_9_18_end:
__sbr_cell_9_19:
    add rsi, 1280
__sbr_cell_9_19_end:
__sbr_cell_9_20:
    add rcx, 4
__sbr_cell_9_20_end:
__sbr_cell_9_21:
    jne ff_sbr_hf_g_filt_sse.loop4
__sbr_cell_9_21_end:
__sbr_cell_9_22:
    and r9, 3
__sbr_cell_9_22_end:
__sbr_cell_9_23:
    je ff_sbr_hf_g_filt_sse.end
__sbr_cell_9_23_end:
ff_sbr_hf_g_filt_sse.loop1:
__sbr_cell_9_24:
    movss xmm0, DWORD PTR [rdx+0]
__sbr_cell_9_24_end:
__sbr_cell_9_25:
    movlps xmm2, QWORD PTR [rsi+0]
__sbr_cell_9_25_end:
__sbr_cell_9_26:
    unpcklps xmm0, xmm0
__sbr_cell_9_26_end:
__sbr_cell_9_27:
    mulps xmm2, xmm0
__sbr_cell_9_27_end:
__sbr_cell_9_28:
    movlps QWORD PTR [rdi+0], xmm2
__sbr_cell_9_28_end:
__sbr_cell_9_29:
    add rdi, 8
__sbr_cell_9_29_end:
__sbr_cell_9_30:
    add rdx, 4
__sbr_cell_9_30_end:
__sbr_cell_9_31:
    add rsi, 320
__sbr_cell_9_31_end:
__sbr_cell_9_32:
    dec r9
__sbr_cell_9_32_end:
__sbr_cell_9_33:
    jne ff_sbr_hf_g_filt_sse.loop1
__sbr_cell_9_33_end:
ff_sbr_hf_g_filt_sse.end:
__sbr_cell_9_34:
    ret
__sbr_cell_9_34_end:
.size ff_sbr_hf_g_filt_sse, .-ff_sbr_hf_g_filt_sse
.section .text.ff_sbr_hf_gen_sse,"ax",@progbits
.globl ff_sbr_hf_gen_sse
.type ff_sbr_hf_gen_sse,@function
ff_sbr_hf_gen_sse:
__sbr_cell_10_0:
    movlps xmm2, QWORD PTR [rcx+0]
__sbr_cell_10_0_end:
__sbr_cell_10_1:
    movlps xmm1, QWORD PTR [rdx+0]
__sbr_cell_10_1_end:
__sbr_cell_10_2:
    shufps xmm0, xmm0, 0
__sbr_cell_10_2_end:
__sbr_cell_10_3:
    mulps xmm2, xmm0
__sbr_cell_10_3_end:
__sbr_cell_10_4:
    mulps xmm1, xmm0
__sbr_cell_10_4_end:
__sbr_cell_10_5:
    mulps xmm2, xmm0
__sbr_cell_10_5_end:
__sbr_cell_10_6:
    movaps xmm3, xmm1
__sbr_cell_10_6_end:
__sbr_cell_10_7:
    movaps xmm4, xmm2
__sbr_cell_10_7_end:
__sbr_cell_10_8:
    movsxd r8, r8d
__sbr_cell_10_8_end:
__sbr_cell_10_9:
    movsxd r9, r9d
__sbr_cell_10_9_end:
__sbr_cell_10_10:
    sub r8, r9
__sbr_cell_10_10_end:
__sbr_cell_10_11:
    lea rdi, [rdi+r9*8+0]
__sbr_cell_10_11_end:
__sbr_cell_10_12:
    lea rsi, [rsi+r9*8-16]
__sbr_cell_10_12_end:
__sbr_cell_10_13:
    shl r8, 3
__sbr_cell_10_13_end:
ff_sbr_hf_gen_sse.pre:
__sbr_cell_10_14:
    movaps xmm0, XMMWORD PTR [rsi+r8*1+0]
__sbr_cell_10_14_end:
__sbr_cell_10_15:
    shufps xmm3, xmm3, 85
__sbr_cell_10_15_end:
__sbr_cell_10_16:
    shufps xmm4, xmm4, 85
__sbr_cell_10_16_end:
__sbr_cell_10_17:
    xorps xmm3, XMMWORD PTR [rip+ps_mask]
__sbr_cell_10_17_end:
__sbr_cell_10_18:
    shufps xmm1, xmm1, 0
__sbr_cell_10_18_end:
__sbr_cell_10_19:
    shufps xmm2, xmm2, 0
__sbr_cell_10_19_end:
__sbr_cell_10_20:
    xorps xmm4, XMMWORD PTR [rip+ps_mask]
__sbr_cell_10_20_end:
ff_sbr_hf_gen_sse.loop2:
__sbr_cell_10_21:
    movups xmm7, XMMWORD PTR [rsi+r8*1+8]
__sbr_cell_10_21_end:
__sbr_cell_10_22:
    movaps xmm6, xmm0
__sbr_cell_10_22_end:
__sbr_cell_10_23:
    movaps xmm5, xmm7
__sbr_cell_10_23_end:
__sbr_cell_10_24:
    shufps xmm0, xmm0, 177
__sbr_cell_10_24_end:
__sbr_cell_10_25:
    shufps xmm7, xmm7, 177
__sbr_cell_10_25_end:
__sbr_cell_10_26:
    mulps xmm0, xmm4
__sbr_cell_10_26_end:
__sbr_cell_10_27:
    mulps xmm7, xmm3
__sbr_cell_10_27_end:
__sbr_cell_10_28:
    mulps xmm6, xmm2
__sbr_cell_10_28_end:
__sbr_cell_10_29:
    mulps xmm5, xmm1
__sbr_cell_10_29_end:
__sbr_cell_10_30:
    addps xmm7, xmm0
__sbr_cell_10_30_end:
__sbr_cell_10_31:
    movaps xmm0, XMMWORD PTR [rsi+r8*1+16]
__sbr_cell_10_31_end:
__sbr_cell_10_32:
    addps xmm7, xmm0
__sbr_cell_10_32_end:
__sbr_cell_10_33:
    addps xmm6, xmm5
__sbr_cell_10_33_end:
__sbr_cell_10_34:
    addps xmm7, xmm6
__sbr_cell_10_34_end:
__sbr_cell_10_35:
    movaps XMMWORD PTR [rdi+r8*1+0], xmm7
__sbr_cell_10_35_end:
__sbr_cell_10_36:
    add r8, 16
__sbr_cell_10_36_end:
__sbr_cell_10_37:
    jne ff_sbr_hf_gen_sse.loop2
__sbr_cell_10_37_end:
ff_sbr_hf_gen_sse.done:
__sbr_cell_10_38:
    ret
__sbr_cell_10_38_end:
.size ff_sbr_hf_gen_sse, .-ff_sbr_hf_gen_sse
.section .text.ff_sbr_neg_odd_64_sse,"ax",@progbits
.globl ff_sbr_neg_odd_64_sse
.type ff_sbr_neg_odd_64_sse,@function
ff_sbr_neg_odd_64_sse:
__sbr_cell_11_0:
    lea rsi, [rdi+256]
__sbr_cell_11_0_end:
ff_sbr_neg_odd_64_sse.loop:
__sbr_cell_11_1:
    movaps xmm0, XMMWORD PTR [rdi+0]
__sbr_cell_11_1_end:
__sbr_cell_11_2:
    movaps xmm1, XMMWORD PTR [rdi+16]
__sbr_cell_11_2_end:
__sbr_cell_11_3:
    movaps xmm2, XMMWORD PTR [rdi+32]
__sbr_cell_11_3_end:
__sbr_cell_11_4:
    movaps xmm3, XMMWORD PTR [rdi+48]
__sbr_cell_11_4_end:
__sbr_cell_11_5:
    xorps xmm0, XMMWORD PTR [rip+ps_mask2]
__sbr_cell_11_5_end:
__sbr_cell_11_6:
    xorps xmm1, XMMWORD PTR [rip+ps_mask2]
__sbr_cell_11_6_end:
__sbr_cell_11_7:
    xorps xmm2, XMMWORD PTR [rip+ps_mask2]
__sbr_cell_11_7_end:
__sbr_cell_11_8:
    xorps xmm3, XMMWORD PTR [rip+ps_mask2]
__sbr_cell_11_8_end:
__sbr_cell_11_9:
    movaps XMMWORD PTR [rdi+0], xmm0
__sbr_cell_11_9_end:
__sbr_cell_11_10:
    movaps XMMWORD PTR [rdi+16], xmm1
__sbr_cell_11_10_end:
__sbr_cell_11_11:
    movaps XMMWORD PTR [rdi+32], xmm2
__sbr_cell_11_11_end:
__sbr_cell_11_12:
    movaps XMMWORD PTR [rdi+48], xmm3
__sbr_cell_11_12_end:
__sbr_cell_11_13:
    add rdi, 64
__sbr_cell_11_13_end:
__sbr_cell_11_14:
    cmp rdi, rsi
__sbr_cell_11_14_end:
__sbr_cell_11_15:
    jne ff_sbr_neg_odd_64_sse.loop
__sbr_cell_11_15_end:
ff_sbr_neg_odd_64_sse.done:
__sbr_cell_11_16:
    ret
__sbr_cell_11_16_end:
.size ff_sbr_neg_odd_64_sse, .-ff_sbr_neg_odd_64_sse
.section .text.ff_sbr_qmf_deint_bfly_sse2,"ax",@progbits
.globl ff_sbr_qmf_deint_bfly_sse2
.type ff_sbr_qmf_deint_bfly_sse2,@function
ff_sbr_qmf_deint_bfly_sse2:
__sbr_cell_12_0:
    mov r8d, 224
__sbr_cell_12_0_end:
__sbr_cell_12_1:
    lea rcx, [rdi+256]
__sbr_cell_12_1_end:
ff_sbr_qmf_deint_bfly_sse2.loop:
__sbr_cell_12_2:
    movdqa xmm0, XMMWORD PTR [rsi+r8*1+0]
__sbr_cell_12_2_end:
__sbr_cell_12_3:
    movdqa xmm1, XMMWORD PTR [rdx+0]
__sbr_cell_12_3_end:
__sbr_cell_12_4:
    movdqa xmm4, XMMWORD PTR [rsi+r8*1+16]
__sbr_cell_12_4_end:
__sbr_cell_12_5:
    movdqa xmm5, XMMWORD PTR [rdx+16]
__sbr_cell_12_5_end:
__sbr_cell_12_6:
    pshufd xmm2, xmm0, 27
__sbr_cell_12_6_end:
__sbr_cell_12_7:
    pshufd xmm3, xmm1, 27
__sbr_cell_12_7_end:
__sbr_cell_12_8:
    pshufd xmm6, xmm4, 27
__sbr_cell_12_8_end:
__sbr_cell_12_9:
    pshufd xmm7, xmm5, 27
__sbr_cell_12_9_end:
__sbr_cell_12_10:
    addps xmm5, xmm2
__sbr_cell_12_10_end:
__sbr_cell_12_11:
    subps xmm0, xmm7
__sbr_cell_12_11_end:
__sbr_cell_12_12:
    addps xmm1, xmm6
__sbr_cell_12_12_end:
__sbr_cell_12_13:
    subps xmm4, xmm3
__sbr_cell_12_13_end:
__sbr_cell_12_14:
    movdqa XMMWORD PTR [rcx+0], xmm1
__sbr_cell_12_14_end:
__sbr_cell_12_15:
    movdqa XMMWORD PTR [rcx+16], xmm5
__sbr_cell_12_15_end:
__sbr_cell_12_16:
    movdqa XMMWORD PTR [rdi+r8*1+0], xmm0
__sbr_cell_12_16_end:
__sbr_cell_12_17:
    movdqa XMMWORD PTR [rdi+r8*1+16], xmm4
__sbr_cell_12_17_end:
__sbr_cell_12_18:
    add rdx, 32
__sbr_cell_12_18_end:
__sbr_cell_12_19:
    add rcx, 32
__sbr_cell_12_19_end:
__sbr_cell_12_20:
    sub r8, 32
__sbr_cell_12_20_end:
__sbr_cell_12_21:
    jge ff_sbr_qmf_deint_bfly_sse2.loop
__sbr_cell_12_21_end:
ff_sbr_qmf_deint_bfly_sse2.done:
__sbr_cell_12_22:
    ret
__sbr_cell_12_22_end:
.size ff_sbr_qmf_deint_bfly_sse2, .-ff_sbr_qmf_deint_bfly_sse2
.section .text.ff_sbr_qmf_deint_neg_sse,"ax",@progbits
.globl ff_sbr_qmf_deint_neg_sse
.type ff_sbr_qmf_deint_neg_sse,@function
ff_sbr_qmf_deint_neg_sse:
__sbr_cell_13_0:
    mov rcx, -128
__sbr_cell_13_0_end:
__sbr_cell_13_1:
    lea rdx, [rdi+256]
__sbr_cell_13_1_end:
__sbr_cell_13_2:
    add rdi, 112
__sbr_cell_13_2_end:
__sbr_cell_13_3:
    add rsi, 256
__sbr_cell_13_3_end:
__sbr_cell_13_4:
    movaps xmm3, XMMWORD PTR [rip+ff_ps_neg]
__sbr_cell_13_4_end:
ff_sbr_qmf_deint_neg_sse.loop:
__sbr_cell_13_5:
    movaps xmm0, XMMWORD PTR [rsi+rcx*2+0]
__sbr_cell_13_5_end:
__sbr_cell_13_6:
    movaps xmm1, XMMWORD PTR [rsi+rcx*2+16]
__sbr_cell_13_6_end:
__sbr_cell_13_7:
    movaps xmm2, xmm0
__sbr_cell_13_7_end:
__sbr_cell_13_8:
    shufps xmm2, xmm1, 136
__sbr_cell_13_8_end:
__sbr_cell_13_9:
    shufps xmm1, xmm0, 119
__sbr_cell_13_9_end:
__sbr_cell_13_10:
    xorps xmm2, xmm3
__sbr_cell_13_10_end:
__sbr_cell_13_11:
    movaps XMMWORD PTR [rdi+0], xmm1
__sbr_cell_13_11_end:
__sbr_cell_13_12:
    movaps XMMWORD PTR [rdx+rcx*1+0], xmm2
__sbr_cell_13_12_end:
__sbr_cell_13_13:
    sub rdi, 16
__sbr_cell_13_13_end:
__sbr_cell_13_14:
    add rcx, 16
__sbr_cell_13_14_end:
__sbr_cell_13_15:
    jl ff_sbr_qmf_deint_neg_sse.loop
__sbr_cell_13_15_end:
ff_sbr_qmf_deint_neg_sse.done:
__sbr_cell_13_16:
    ret
__sbr_cell_13_16_end:
.size ff_sbr_qmf_deint_neg_sse, .-ff_sbr_qmf_deint_neg_sse
.section .text.ff_sbr_qmf_post_shuffle_sse,"ax",@progbits
.globl ff_sbr_qmf_post_shuffle_sse
.type ff_sbr_qmf_post_shuffle_sse,@function
ff_sbr_qmf_post_shuffle_sse:
__sbr_cell_14_0:
    lea rdx, [rsi+240]
__sbr_cell_14_0_end:
__sbr_cell_14_1:
    movaps xmm3, XMMWORD PTR [rip+ff_ps_neg]
__sbr_cell_14_1_end:
ff_sbr_qmf_post_shuffle_sse.loop:
__sbr_cell_14_2:
    movaps xmm1, XMMWORD PTR [rsi+0]
__sbr_cell_14_2_end:
__sbr_cell_14_3:
    movaps xmm0, XMMWORD PTR [rdx+0]
__sbr_cell_14_3_end:
__sbr_cell_14_4:
    xorps xmm0, xmm3
__sbr_cell_14_4_end:
__sbr_cell_14_5:
    shufps xmm0, xmm0, 27
__sbr_cell_14_5_end:
__sbr_cell_14_6:
    movaps xmm2, xmm0
__sbr_cell_14_6_end:
__sbr_cell_14_7:
    unpcklps xmm2, xmm1
__sbr_cell_14_7_end:
__sbr_cell_14_8:
    unpckhps xmm0, xmm1
__sbr_cell_14_8_end:
__sbr_cell_14_9:
    movaps XMMWORD PTR [rdi+0], xmm2
__sbr_cell_14_9_end:
__sbr_cell_14_10:
    movaps XMMWORD PTR [rdi+16], xmm0
__sbr_cell_14_10_end:
ff_sbr_qmf_post_shuffle_sse.step:
__sbr_cell_14_11:
    add rdi, 32
__sbr_cell_14_11_end:
__sbr_cell_14_12:
    sub rdx, 16
__sbr_cell_14_12_end:
__sbr_cell_14_13:
    add rsi, 16
__sbr_cell_14_13_end:
ff_sbr_qmf_post_shuffle_sse.cmp:
__sbr_cell_14_14:
    cmp rsi, rdx
__sbr_cell_14_14_end:
__sbr_cell_14_15:
    jl ff_sbr_qmf_post_shuffle_sse.loop
__sbr_cell_14_15_end:
ff_sbr_qmf_post_shuffle_sse.done:
__sbr_cell_14_16:
    ret
__sbr_cell_14_16_end:
.size ff_sbr_qmf_post_shuffle_sse, .-ff_sbr_qmf_post_shuffle_sse
.section .text.ff_sbr_qmf_pre_shuffle_sse2,"ax",@progbits
.globl ff_sbr_qmf_pre_shuffle_sse2
.type ff_sbr_qmf_pre_shuffle_sse2,@function
ff_sbr_qmf_pre_shuffle_sse2:
__sbr_cell_15_0:
    mov ecx, 96
__sbr_cell_15_0_end:
__sbr_cell_15_1:
    lea rsi, [rdi+132]
__sbr_cell_15_1_end:
__sbr_cell_15_2:
    lea rdx, [rdi+256]
__sbr_cell_15_2_end:
__sbr_cell_15_3:
    movdqa xmm5, XMMWORD PTR [rip+ff_ps_neg]
__sbr_cell_15_3_end:
ff_sbr_qmf_pre_shuffle_sse2.loop:
__sbr_cell_15_4:
    movdqu xmm0, XMMWORD PTR [rsi+0]
__sbr_cell_15_4_end:
__sbr_cell_15_5:
    movdqu xmm2, XMMWORD PTR [rsi+16]
__sbr_cell_15_5_end:
__sbr_cell_15_6:
    movdqu xmm1, XMMWORD PTR [rcx+rdi*1+20]
__sbr_cell_15_6_end:
__sbr_cell_15_7:
    movdqu xmm3, XMMWORD PTR [rdi+rcx*1+4]
__sbr_cell_15_7_end:
__sbr_cell_15_8:
    pxor xmm2, xmm5
__sbr_cell_15_8_end:
__sbr_cell_15_9:
    pxor xmm0, xmm5
__sbr_cell_15_9_end:
__sbr_cell_15_10:
    pshufd xmm2, xmm2, 27
__sbr_cell_15_10_end:
__sbr_cell_15_11:
    pshufd xmm0, xmm0, 27
__sbr_cell_15_11_end:
__sbr_cell_15_12:
    movdqa xmm4, xmm2
__sbr_cell_15_12_end:
__sbr_cell_15_13:
    punpckldq xmm2, xmm3
__sbr_cell_15_13_end:
__sbr_cell_15_14:
    punpckhdq xmm4, xmm3
__sbr_cell_15_14_end:
__sbr_cell_15_15:
    movdqa xmm3, xmm0
__sbr_cell_15_15_end:
__sbr_cell_15_16:
    punpckldq xmm0, xmm1
__sbr_cell_15_16_end:
__sbr_cell_15_17:
    punpckhdq xmm3, xmm1
__sbr_cell_15_17_end:
__sbr_cell_15_18:
    movdqa XMMWORD PTR [rdx+rcx*2+0], xmm2
__sbr_cell_15_18_end:
__sbr_cell_15_19:
    movdqa XMMWORD PTR [rdx+rcx*2+16], xmm4
__sbr_cell_15_19_end:
__sbr_cell_15_20:
    movdqa XMMWORD PTR [rdx+rcx*2+32], xmm0
__sbr_cell_15_20_end:
__sbr_cell_15_21:
    movdqa XMMWORD PTR [rdx+rcx*2+48], xmm3
__sbr_cell_15_21_end:
__sbr_cell_15_22:
    add rsi, 32
__sbr_cell_15_22_end:
__sbr_cell_15_23:
    sub rcx, 32
__sbr_cell_15_23_end:
__sbr_cell_15_24:
    jge ff_sbr_qmf_pre_shuffle_sse2.loop
__sbr_cell_15_24_end:
ff_sbr_qmf_pre_shuffle_sse2.tail:
__sbr_cell_15_25:
    movq xmm2, QWORD PTR [rdi+0]
__sbr_cell_15_25_end:
__sbr_cell_15_26:
    movq QWORD PTR [rdx+0], xmm2
__sbr_cell_15_26_end:
ff_sbr_qmf_pre_shuffle_sse2.done:
__sbr_cell_15_27:
    ret
__sbr_cell_15_27_end:
.size ff_sbr_qmf_pre_shuffle_sse2, .-ff_sbr_qmf_pre_shuffle_sse2
.section .text.ff_sbr_sum64x5_sse,"ax",@progbits
.globl ff_sbr_sum64x5_sse
.type ff_sbr_sum64x5_sse,@function
ff_sbr_sum64x5_sse:
__sbr_cell_16_0:
    lea rsi, [rdi+256]
__sbr_cell_16_0_end:
ff_sbr_sum64x5_sse.loop:
__sbr_cell_16_1:
    movaps xmm0, XMMWORD PTR [rdi+0]
__sbr_cell_16_1_end:
__sbr_cell_16_2:
    movaps xmm2, XMMWORD PTR [rdi+16]
__sbr_cell_16_2_end:
__sbr_cell_16_3:
    movaps xmm1, XMMWORD PTR [rdi+256]
__sbr_cell_16_3_end:
__sbr_cell_16_4:
    movaps xmm3, XMMWORD PTR [rdi+272]
__sbr_cell_16_4_end:
__sbr_cell_16_5:
    addps xmm0, XMMWORD PTR [rdi+512]
__sbr_cell_16_5_end:
__sbr_cell_16_6:
    addps xmm2, XMMWORD PTR [rdi+528]
__sbr_cell_16_6_end:
__sbr_cell_16_7:
    addps xmm1, XMMWORD PTR [rdi+768]
__sbr_cell_16_7_end:
__sbr_cell_16_8:
    addps xmm3, XMMWORD PTR [rdi+784]
__sbr_cell_16_8_end:
__sbr_cell_16_9:
    addps xmm0, XMMWORD PTR [rdi+1024]
__sbr_cell_16_9_end:
__sbr_cell_16_10:
    addps xmm2, XMMWORD PTR [rdi+1040]
__sbr_cell_16_10_end:
__sbr_cell_16_11:
    addps xmm0, xmm1
__sbr_cell_16_11_end:
__sbr_cell_16_12:
    addps xmm2, xmm3
__sbr_cell_16_12_end:
__sbr_cell_16_13:
    movaps XMMWORD PTR [rdi+0], xmm0
__sbr_cell_16_13_end:
__sbr_cell_16_14:
    movaps XMMWORD PTR [rdi+16], xmm2
__sbr_cell_16_14_end:
__sbr_cell_16_15:
    add rdi, 32
__sbr_cell_16_15_end:
__sbr_cell_16_16:
    cmp rdi, rsi
__sbr_cell_16_16_end:
__sbr_cell_16_17:
    jne ff_sbr_sum64x5_sse.loop
__sbr_cell_16_17_end:
ff_sbr_sum64x5_sse.done:
__sbr_cell_16_18:
    ret
__sbr_cell_16_18_end:
.size ff_sbr_sum64x5_sse, .-ff_sbr_sum64x5_sse
.section .text.ff_sbr_sum_square_sse,"ax",@progbits
.globl ff_sbr_sum_square_sse
.type ff_sbr_sum_square_sse,@function
ff_sbr_sum_square_sse:
__sbr_cell_17_0:
    mov edx, esi
__sbr_cell_17_0_end:
__sbr_cell_17_1:
    xorps xmm0, xmm0
__sbr_cell_17_1_end:
__sbr_cell_17_2:
    xorps xmm1, xmm1
__sbr_cell_17_2_end:
__sbr_cell_17_3:
    sar rdx, 3
__sbr_cell_17_3_end:
__sbr_cell_17_4:
    je ff_sbr_sum_square_sse.prepare
__sbr_cell_17_4_end:
ff_sbr_sum_square_sse.loop:
__sbr_cell_17_5:
    movups xmm2, XMMWORD PTR [rdi+0]
__sbr_cell_17_5_end:
__sbr_cell_17_6:
    movups xmm3, XMMWORD PTR [rdi+16]
__sbr_cell_17_6_end:
__sbr_cell_17_7:
    movups xmm4, XMMWORD PTR [rdi+32]
__sbr_cell_17_7_end:
__sbr_cell_17_8:
    movups xmm5, XMMWORD PTR [rdi+48]
__sbr_cell_17_8_end:
__sbr_cell_17_9:
    mulps xmm2, xmm2
__sbr_cell_17_9_end:
__sbr_cell_17_10:
    mulps xmm3, xmm3
__sbr_cell_17_10_end:
__sbr_cell_17_11:
    mulps xmm4, xmm4
__sbr_cell_17_11_end:
__sbr_cell_17_12:
    mulps xmm5, xmm5
__sbr_cell_17_12_end:
__sbr_cell_17_13:
    addps xmm0, xmm2
__sbr_cell_17_13_end:
__sbr_cell_17_14:
    addps xmm1, xmm3
__sbr_cell_17_14_end:
__sbr_cell_17_15:
    addps xmm0, xmm4
__sbr_cell_17_15_end:
__sbr_cell_17_16:
    addps xmm1, xmm5
__sbr_cell_17_16_end:
__sbr_cell_17_17:
    add rdi, 64
__sbr_cell_17_17_end:
__sbr_cell_17_18:
    dec rdx
__sbr_cell_17_18_end:
__sbr_cell_17_19:
    jne ff_sbr_sum_square_sse.loop
__sbr_cell_17_19_end:
ff_sbr_sum_square_sse.prepare:
__sbr_cell_17_20:
    and rsi, 7
__sbr_cell_17_20_end:
__sbr_cell_17_21:
    sar rsi, 1
__sbr_cell_17_21_end:
__sbr_cell_17_22:
    je ff_sbr_sum_square_sse.end
__sbr_cell_17_22_end:
ff_sbr_sum_square_sse.endloop:
__sbr_cell_17_23:
    movups xmm2, XMMWORD PTR [rdi+0]
__sbr_cell_17_23_end:
__sbr_cell_17_24:
    add rdi, 16
__sbr_cell_17_24_end:
__sbr_cell_17_25:
    mulps xmm2, xmm2
__sbr_cell_17_25_end:
__sbr_cell_17_26:
    dec rsi
__sbr_cell_17_26_end:
__sbr_cell_17_27:
    addps xmm0, xmm2
__sbr_cell_17_27_end:
__sbr_cell_17_28:
    jne ff_sbr_sum_square_sse.endloop
__sbr_cell_17_28_end:
ff_sbr_sum_square_sse.end:
__sbr_cell_17_29:
    addps xmm0, xmm1
__sbr_cell_17_29_end:
__sbr_cell_17_30:
    movhlps xmm2, xmm0
__sbr_cell_17_30_end:
__sbr_cell_17_31:
    addps xmm0, xmm2
__sbr_cell_17_31_end:
__sbr_cell_17_32:
    movss xmm1, xmm0
__sbr_cell_17_32_end:
__sbr_cell_17_33:
    shufps xmm0, xmm0, 1
__sbr_cell_17_33_end:
__sbr_cell_17_34:
    addss xmm0, xmm1
__sbr_cell_17_34_end:
ff_sbr_sum_square_sse.done:
__sbr_cell_17_35:
    ret
__sbr_cell_17_35_end:
.size ff_sbr_sum_square_sse, .-ff_sbr_sum_square_sse
.section .text.ff_vector_fmul_add_avx,"ax",@progbits
.globl ff_vector_fmul_add_avx
.type ff_vector_fmul_add_avx,@function
ff_vector_fmul_add_avx:
__sbr_cell_18_0:
    lea r8, [r8d*4-64]
__sbr_cell_18_0_end:
__sbr_cell_18_1:
    .nops 7
__sbr_cell_18_1_end:
ff_vector_fmul_add_avx.loop:
__sbr_cell_18_2:
    vmovaps ymm0, YMMWORD PTR [rsi+r8*1+0]
__sbr_cell_18_2_end:
__sbr_cell_18_3:
    vmovaps ymm1, YMMWORD PTR [rsi+r8*1+32]
__sbr_cell_18_3_end:
__sbr_cell_18_4:
    vmulps ymm0, ymm0, YMMWORD PTR [rdx+r8*1+0]
__sbr_cell_18_4_end:
__sbr_cell_18_5:
    vmulps ymm1, ymm1, YMMWORD PTR [rdx+r8*1+32]
__sbr_cell_18_5_end:
__sbr_cell_18_6:
    vaddps ymm0, ymm0, YMMWORD PTR [rcx+r8*1+0]
__sbr_cell_18_6_end:
__sbr_cell_18_7:
    vaddps ymm1, ymm1, YMMWORD PTR [rcx+r8*1+32]
__sbr_cell_18_7_end:
__sbr_cell_18_8:
    vmovaps YMMWORD PTR [rdi+r8*1+0], ymm0
__sbr_cell_18_8_end:
__sbr_cell_18_9:
    vmovaps YMMWORD PTR [rdi+r8*1+32], ymm1
__sbr_cell_18_9_end:
__sbr_cell_18_10:
    sub r8, 64
__sbr_cell_18_10_end:
__sbr_cell_18_11:
    jge ff_vector_fmul_add_avx.loop
__sbr_cell_18_11_end:
ff_vector_fmul_add_avx.done:
__sbr_cell_18_12:
    vzeroupper
__sbr_cell_18_12_end:
__sbr_cell_18_13:
    ret
__sbr_cell_18_13_end:
.size ff_vector_fmul_add_avx, .-ff_vector_fmul_add_avx
.section .text.ff_vector_fmul_add_fma3,"ax",@progbits
.globl ff_vector_fmul_add_fma3
.type ff_vector_fmul_add_fma3,@function
ff_vector_fmul_add_fma3:
__sbr_cell_19_0:
    lea r8, [r8d*4-64]
__sbr_cell_19_0_end:
__sbr_cell_19_1:
    .nops 7
__sbr_cell_19_1_end:
ff_vector_fmul_add_fma3.loop:
__sbr_cell_19_2:
    vmovaps ymm0, YMMWORD PTR [rsi+r8*1+0]
__sbr_cell_19_2_end:
__sbr_cell_19_3:
    vmovaps ymm1, YMMWORD PTR [rsi+r8*1+32]
__sbr_cell_19_3_end:
__sbr_cell_19_4:
    vmovaps ymm2, YMMWORD PTR [rcx+r8*1+0]
__sbr_cell_19_4_end:
__sbr_cell_19_5:
    vmovaps ymm3, YMMWORD PTR [rcx+r8*1+32]
__sbr_cell_19_5_end:
__sbr_cell_19_6:
    vfmadd132ps ymm0, ymm2, YMMWORD PTR [rdx+r8*1+0]
__sbr_cell_19_6_end:
__sbr_cell_19_7:
    vfmadd132ps ymm1, ymm3, YMMWORD PTR [rdx+r8*1+32]
__sbr_cell_19_7_end:
__sbr_cell_19_8:
    vmovaps YMMWORD PTR [rdi+r8*1+0], ymm0
__sbr_cell_19_8_end:
__sbr_cell_19_9:
    vmovaps YMMWORD PTR [rdi+r8*1+32], ymm1
__sbr_cell_19_9_end:
__sbr_cell_19_10:
    sub r8, 64
__sbr_cell_19_10_end:
__sbr_cell_19_11:
    jge ff_vector_fmul_add_fma3.loop
__sbr_cell_19_11_end:
ff_vector_fmul_add_fma3.done:
__sbr_cell_19_12:
    vzeroupper
__sbr_cell_19_12_end:
__sbr_cell_19_13:
    ret
__sbr_cell_19_13_end:
.size ff_vector_fmul_add_fma3, .-ff_vector_fmul_add_fma3
.section .text.ff_vector_fmul_add_sse,"ax",@progbits
.globl ff_vector_fmul_add_sse
.type ff_vector_fmul_add_sse,@function
ff_vector_fmul_add_sse:
__sbr_cell_20_0:
    lea r8, [r8d*4-32]
__sbr_cell_20_0_end:
__sbr_cell_20_1:
    .nops 7
__sbr_cell_20_1_end:
ff_vector_fmul_add_sse.loop:
__sbr_cell_20_2:
    movaps xmm0, XMMWORD PTR [rsi+r8*1+0]
__sbr_cell_20_2_end:
__sbr_cell_20_3:
    movaps xmm1, XMMWORD PTR [rsi+r8*1+16]
__sbr_cell_20_3_end:
__sbr_cell_20_4:
    mulps xmm0, XMMWORD PTR [rdx+r8*1+0]
__sbr_cell_20_4_end:
__sbr_cell_20_5:
    mulps xmm1, XMMWORD PTR [rdx+r8*1+16]
__sbr_cell_20_5_end:
__sbr_cell_20_6:
    addps xmm0, XMMWORD PTR [rcx+r8*1+0]
__sbr_cell_20_6_end:
__sbr_cell_20_7:
    addps xmm1, XMMWORD PTR [rcx+r8*1+16]
__sbr_cell_20_7_end:
__sbr_cell_20_8:
    movaps XMMWORD PTR [rdi+r8*1+0], xmm0
__sbr_cell_20_8_end:
__sbr_cell_20_9:
    movaps XMMWORD PTR [rdi+r8*1+16], xmm1
__sbr_cell_20_9_end:
__sbr_cell_20_10:
    sub r8, 32
__sbr_cell_20_10_end:
__sbr_cell_20_11:
    jge ff_vector_fmul_add_sse.loop
__sbr_cell_20_11_end:
ff_vector_fmul_add_sse.done:
__sbr_cell_20_12:
    ret
__sbr_cell_20_12_end:
.size ff_vector_fmul_add_sse, .-ff_vector_fmul_add_sse
.section .text.ff_vector_fmul_avx,"ax",@progbits
.globl ff_vector_fmul_avx
.type ff_vector_fmul_avx,@function
ff_vector_fmul_avx:
__sbr_cell_21_0:
    lea rcx, [ecx*4-64]
__sbr_cell_21_0_end:
__sbr_cell_21_1:
    .nops 7
__sbr_cell_21_1_end:
ff_vector_fmul_avx.loop:
__sbr_cell_21_2:
    vmovaps ymm0, YMMWORD PTR [rsi+rcx*1+0]
__sbr_cell_21_2_end:
__sbr_cell_21_3:
    vmovaps ymm1, YMMWORD PTR [rcx+rsi*1+32]
__sbr_cell_21_3_end:
__sbr_cell_21_4:
    vmulps ymm0, ymm0, YMMWORD PTR [rdx+rcx*1+0]
__sbr_cell_21_4_end:
__sbr_cell_21_5:
    vmulps ymm1, ymm1, YMMWORD PTR [rcx+rdx*1+32]
__sbr_cell_21_5_end:
__sbr_cell_21_6:
    vmovaps YMMWORD PTR [rdi+rcx*1+0], ymm0
__sbr_cell_21_6_end:
__sbr_cell_21_7:
    vmovaps YMMWORD PTR [rcx+rdi*1+32], ymm1
__sbr_cell_21_7_end:
__sbr_cell_21_8:
    sub rcx, 64
__sbr_cell_21_8_end:
__sbr_cell_21_9:
    jge ff_vector_fmul_avx.loop
__sbr_cell_21_9_end:
ff_vector_fmul_avx.done:
__sbr_cell_21_10:
    vzeroupper
__sbr_cell_21_10_end:
__sbr_cell_21_11:
    ret
__sbr_cell_21_11_end:
.size ff_vector_fmul_avx, .-ff_vector_fmul_avx
.section .text.ff_vector_fmul_reverse_avx,"ax",@progbits
.globl ff_vector_fmul_reverse_avx
.type ff_vector_fmul_reverse_avx,@function
ff_vector_fmul_reverse_avx:
__sbr_cell_22_0:
    lea rcx, [ecx*4-64]
__sbr_cell_22_0_end:
__sbr_cell_22_1:
    .nops 7
__sbr_cell_22_1_end:
ff_vector_fmul_reverse_avx.loop:
__sbr_cell_22_2:
    vmovaps xmm0, XMMWORD PTR [rdx+16]
__sbr_cell_22_2_end:
__sbr_cell_22_3:
    vinsertf128 ymm0, ymm0, XMMWORD PTR [rdx+0], 1
__sbr_cell_22_3_end:
__sbr_cell_22_4:
    vshufps ymm0, ymm0, ymm0, 27
__sbr_cell_22_4_end:
__sbr_cell_22_5:
    vmovaps xmm1, XMMWORD PTR [rdx+48]
__sbr_cell_22_5_end:
__sbr_cell_22_6:
    vinsertf128 ymm1, ymm1, XMMWORD PTR [rdx+32], 1
__sbr_cell_22_6_end:
__sbr_cell_22_7:
    vshufps ymm1, ymm1, ymm1, 27
__sbr_cell_22_7_end:
__sbr_cell_22_8:
    vmulps ymm0, ymm0, YMMWORD PTR [rsi+rcx*1+32]
__sbr_cell_22_8_end:
__sbr_cell_22_9:
    vmulps ymm1, ymm1, YMMWORD PTR [rsi+rcx*1+0]
__sbr_cell_22_9_end:
__sbr_cell_22_10:
    vmovaps YMMWORD PTR [rdi+rcx*1+32], ymm0
__sbr_cell_22_10_end:
__sbr_cell_22_11:
    vmovaps YMMWORD PTR [rdi+rcx*1+0], ymm1
__sbr_cell_22_11_end:
__sbr_cell_22_12:
    add rdx, 64
__sbr_cell_22_12_end:
__sbr_cell_22_13:
    sub rcx, 64
__sbr_cell_22_13_end:
__sbr_cell_22_14:
    jge ff_vector_fmul_reverse_avx.loop
__sbr_cell_22_14_end:
ff_vector_fmul_reverse_avx.done:
__sbr_cell_22_15:
    vzeroupper
__sbr_cell_22_15_end:
__sbr_cell_22_16:
    ret
__sbr_cell_22_16_end:
.size ff_vector_fmul_reverse_avx, .-ff_vector_fmul_reverse_avx
.section .text.ff_vector_fmul_reverse_avx2,"ax",@progbits
.globl ff_vector_fmul_reverse_avx2
.type ff_vector_fmul_reverse_avx2,@function
ff_vector_fmul_reverse_avx2:
__sbr_cell_23_0:
    vmovaps ymm2, YMMWORD PTR [rip+pd_reverse]
__sbr_cell_23_0_end:
ff_vector_fmul_reverse_avx2.lea:
__sbr_cell_23_1:
    lea rcx, [ecx*4-64]
__sbr_cell_23_1_end:
__sbr_cell_23_2:
    .nops 8
__sbr_cell_23_2_end:
__sbr_cell_23_3:
    .nops 7
__sbr_cell_23_3_end:
ff_vector_fmul_reverse_avx2.loop:
__sbr_cell_23_4:
    vpermps ymm0, ymm2, YMMWORD PTR [rdx+0]
__sbr_cell_23_4_end:
__sbr_cell_23_5:
    vpermps ymm1, ymm2, YMMWORD PTR [rdx+32]
__sbr_cell_23_5_end:
__sbr_cell_23_6:
    vmulps ymm0, ymm0, YMMWORD PTR [rsi+rcx*1+32]
__sbr_cell_23_6_end:
__sbr_cell_23_7:
    vmulps ymm1, ymm1, YMMWORD PTR [rsi+rcx*1+0]
__sbr_cell_23_7_end:
__sbr_cell_23_8:
    vmovaps YMMWORD PTR [rdi+rcx*1+32], ymm0
__sbr_cell_23_8_end:
__sbr_cell_23_9:
    vmovaps YMMWORD PTR [rdi+rcx*1+0], ymm1
__sbr_cell_23_9_end:
__sbr_cell_23_10:
    add rdx, 64
__sbr_cell_23_10_end:
__sbr_cell_23_11:
    sub rcx, 64
__sbr_cell_23_11_end:
__sbr_cell_23_12:
    jge ff_vector_fmul_reverse_avx2.loop
__sbr_cell_23_12_end:
ff_vector_fmul_reverse_avx2.done:
__sbr_cell_23_13:
    vzeroupper
__sbr_cell_23_13_end:
__sbr_cell_23_14:
    ret
__sbr_cell_23_14_end:
.size ff_vector_fmul_reverse_avx2, .-ff_vector_fmul_reverse_avx2
.section .text.ff_vector_fmul_reverse_sse,"ax",@progbits
.globl ff_vector_fmul_reverse_sse
.type ff_vector_fmul_reverse_sse,@function
ff_vector_fmul_reverse_sse:
__sbr_cell_24_0:
    lea rcx, [ecx*4-32]
__sbr_cell_24_0_end:
__sbr_cell_24_1:
    .nops 7
__sbr_cell_24_1_end:
ff_vector_fmul_reverse_sse.loop:
__sbr_cell_24_2:
    movaps xmm0, XMMWORD PTR [rdx+0]
__sbr_cell_24_2_end:
__sbr_cell_24_3:
    movaps xmm1, XMMWORD PTR [rdx+16]
__sbr_cell_24_3_end:
__sbr_cell_24_4:
    shufps xmm0, xmm0, 27
__sbr_cell_24_4_end:
__sbr_cell_24_5:
    shufps xmm1, xmm1, 27
__sbr_cell_24_5_end:
__sbr_cell_24_6:
    mulps xmm0, XMMWORD PTR [rsi+rcx*1+16]
__sbr_cell_24_6_end:
__sbr_cell_24_7:
    mulps xmm1, XMMWORD PTR [rsi+rcx*1+0]
__sbr_cell_24_7_end:
__sbr_cell_24_8:
    movaps XMMWORD PTR [rdi+rcx*1+16], xmm0
__sbr_cell_24_8_end:
__sbr_cell_24_9:
    movaps XMMWORD PTR [rdi+rcx*1+0], xmm1
__sbr_cell_24_9_end:
__sbr_cell_24_10:
    add rdx, 32
__sbr_cell_24_10_end:
__sbr_cell_24_11:
    sub rcx, 32
__sbr_cell_24_11_end:
__sbr_cell_24_12:
    jge ff_vector_fmul_reverse_sse.loop
__sbr_cell_24_12_end:
ff_vector_fmul_reverse_sse.done:
__sbr_cell_24_13:
    ret
__sbr_cell_24_13_end:
.size ff_vector_fmul_reverse_sse, .-ff_vector_fmul_reverse_sse
.section .text.ff_vector_fmul_sse,"ax",@progbits
.globl ff_vector_fmul_sse
.type ff_vector_fmul_sse,@function
ff_vector_fmul_sse:
__sbr_cell_25_0:
    lea rcx, [ecx*4-64]
__sbr_cell_25_0_end:
__sbr_cell_25_1:
    .nops 7
__sbr_cell_25_1_end:
ff_vector_fmul_sse.loop:
__sbr_cell_25_2:
    movaps xmm0, XMMWORD PTR [rsi+rcx*1+0]
__sbr_cell_25_2_end:
__sbr_cell_25_3:
    movaps xmm1, XMMWORD PTR [rcx+rsi*1+16]
__sbr_cell_25_3_end:
__sbr_cell_25_4:
    mulps xmm0, XMMWORD PTR [rdx+rcx*1+0]
__sbr_cell_25_4_end:
__sbr_cell_25_5:
    mulps xmm1, XMMWORD PTR [rcx+rdx*1+16]
__sbr_cell_25_5_end:
__sbr_cell_25_6:
    movaps XMMWORD PTR [rdi+rcx*1+0], xmm0
__sbr_cell_25_6_end:
__sbr_cell_25_7:
    movaps XMMWORD PTR [rcx+rdi*1+16], xmm1
__sbr_cell_25_7_end:
ff_vector_fmul_sse.loop2:
__sbr_cell_25_8:
    movaps xmm0, XMMWORD PTR [rcx+rsi*1+32]
__sbr_cell_25_8_end:
__sbr_cell_25_9:
    movaps xmm1, XMMWORD PTR [rcx+rsi*1+48]
__sbr_cell_25_9_end:
__sbr_cell_25_10:
    mulps xmm0, XMMWORD PTR [rcx+rdx*1+32]
__sbr_cell_25_10_end:
__sbr_cell_25_11:
    mulps xmm1, XMMWORD PTR [rcx+rdx*1+48]
__sbr_cell_25_11_end:
__sbr_cell_25_12:
    movaps XMMWORD PTR [rcx+rdi*1+32], xmm0
__sbr_cell_25_12_end:
__sbr_cell_25_13:
    movaps XMMWORD PTR [rcx+rdi*1+48], xmm1
__sbr_cell_25_13_end:
__sbr_cell_25_14:
    sub rcx, 64
__sbr_cell_25_14_end:
__sbr_cell_25_15:
    jge ff_vector_fmul_sse.loop
__sbr_cell_25_15_end:
ff_vector_fmul_sse.done:
__sbr_cell_25_16:
    ret
__sbr_cell_25_16_end:
.size ff_vector_fmul_sse, .-ff_vector_fmul_sse
.section .text.read_sbr_dtdf,"ax",@progbits
.globl read_sbr_dtdf
.type read_sbr_dtdf,@function
read_sbr_dtdf:
__sbr_cell_26_0:
    test edi, edi
__sbr_cell_26_0_end:
__sbr_cell_26_1:
    je read_sbr_dtdf.L5185
__sbr_cell_26_1_end:
__sbr_cell_26_2:
    test ecx, ecx
__sbr_cell_26_2_end:
__sbr_cell_26_3:
    je read_sbr_dtdf.L51a2
__sbr_cell_26_3_end:
__sbr_cell_26_4:
    mov BYTE PTR [rdx+28], 0
__sbr_cell_26_4_end:
__sbr_cell_26_5:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_26_5_end:
__sbr_cell_26_6:
    dec eax
__sbr_cell_26_6_end:
__sbr_cell_26_7:
    test eax, eax
__sbr_cell_26_7_end:
__sbr_cell_26_8:
    jle read_sbr_dtdf.L5272
__sbr_cell_26_8_end:
__sbr_cell_26_9:
    cmp eax, 1
__sbr_cell_26_9_end:
__sbr_cell_26_10:
    jne read_sbr_dtdf.L51bf
__sbr_cell_26_10_end:
__sbr_cell_26_11:
    xor eax, eax
__sbr_cell_26_11_end:
__sbr_cell_26_12:
    jmp read_sbr_dtdf.L5243
__sbr_cell_26_12_end:
read_sbr_dtdf.L5185:
__sbr_cell_26_13:
    movsxd rdi, DWORD PTR [rdx+8]
__sbr_cell_26_13_end:
__sbr_cell_26_14:
    test rdi, rdi
__sbr_cell_26_14_end:
__sbr_cell_26_15:
    jle read_sbr_dtdf.L5402
__sbr_cell_26_15_end:
__sbr_cell_26_16:
    cmp edi, 1
__sbr_cell_26_16_end:
__sbr_cell_26_17:
    jne read_sbr_dtdf.L5347
__sbr_cell_26_17_end:
__sbr_cell_26_18:
    xor eax, eax
__sbr_cell_26_18_end:
__sbr_cell_26_19:
    jmp read_sbr_dtdf.L53d3
__sbr_cell_26_19_end:
read_sbr_dtdf.L51a2:
__sbr_cell_26_20:
    movsxd rdi, DWORD PTR [rdx+8]
__sbr_cell_26_20_end:
__sbr_cell_26_21:
    test rdi, rdi
__sbr_cell_26_21_end:
__sbr_cell_26_22:
    jle read_sbr_dtdf.L5552
__sbr_cell_26_22_end:
__sbr_cell_26_23:
    cmp edi, 1
__sbr_cell_26_23_end:
__sbr_cell_26_24:
    jne read_sbr_dtdf.L54a2
__sbr_cell_26_24_end:
__sbr_cell_26_25:
    xor eax, eax
__sbr_cell_26_25_end:
__sbr_cell_26_26:
    jmp read_sbr_dtdf.L5523
__sbr_cell_26_26_end:
read_sbr_dtdf.L51bf:
__sbr_cell_26_27:
    mov edi, eax
__sbr_cell_26_27_end:
__sbr_cell_26_28:
    mov r8d, edi
__sbr_cell_26_28_end:
__sbr_cell_26_29:
    and r8d, 2147483646
__sbr_cell_26_29_end:
__sbr_cell_26_30:
    xor eax, eax
__sbr_cell_26_30_end:
__sbr_cell_26_31:
    .nops 1
__sbr_cell_26_31_end:
read_sbr_dtdf.L51d0:
__sbr_cell_26_32:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_32_end:
__sbr_cell_26_33:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_33_end:
__sbr_cell_26_34:
    mov r10d, ecx
__sbr_cell_26_34_end:
__sbr_cell_26_35:
    shr r10d, 3
__sbr_cell_26_35_end:
__sbr_cell_26_36:
    xor r11d, r11d
__sbr_cell_26_36_end:
__sbr_cell_26_37:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_37_end:
__sbr_cell_26_38:
    setl r11b
__sbr_cell_26_38_end:
__sbr_cell_26_39:
    add r11d, ecx
__sbr_cell_26_39_end:
__sbr_cell_26_40:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_40_end:
__sbr_cell_26_41:
    and cl, 7
__sbr_cell_26_41_end:
__sbr_cell_26_42:
    shl r9d, cl
__sbr_cell_26_42_end:
__sbr_cell_26_43:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_43_end:
__sbr_cell_26_44:
    shr r9b, 7
__sbr_cell_26_44_end:
__sbr_cell_26_45:
    mov BYTE PTR [rdx+rax*1+29], r9b
__sbr_cell_26_45_end:
read_sbr_dtdf.L5202:
__sbr_cell_26_46:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_46_end:
__sbr_cell_26_47:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_47_end:
__sbr_cell_26_48:
    mov r10d, ecx
__sbr_cell_26_48_end:
__sbr_cell_26_49:
    shr r10d, 3
__sbr_cell_26_49_end:
__sbr_cell_26_50:
    xor r11d, r11d
__sbr_cell_26_50_end:
__sbr_cell_26_51:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_51_end:
__sbr_cell_26_52:
    setl r11b
__sbr_cell_26_52_end:
__sbr_cell_26_53:
    add r11d, ecx
__sbr_cell_26_53_end:
__sbr_cell_26_54:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_54_end:
__sbr_cell_26_55:
    and cl, 7
__sbr_cell_26_55_end:
__sbr_cell_26_56:
    shl r9d, cl
__sbr_cell_26_56_end:
__sbr_cell_26_57:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_57_end:
__sbr_cell_26_58:
    shr r9b, 7
__sbr_cell_26_58_end:
__sbr_cell_26_59:
    mov BYTE PTR [rdx+rax*1+30], r9b
__sbr_cell_26_59_end:
__sbr_cell_26_60:
    add rax, 2
__sbr_cell_26_60_end:
__sbr_cell_26_61:
    cmp r8, rax
__sbr_cell_26_61_end:
__sbr_cell_26_62:
    jne read_sbr_dtdf.L51d0
__sbr_cell_26_62_end:
__sbr_cell_26_63:
    test dil, 1
__sbr_cell_26_63_end:
__sbr_cell_26_64:
    je read_sbr_dtdf.L5272
__sbr_cell_26_64_end:
read_sbr_dtdf.L5243:
__sbr_cell_26_65:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_65_end:
__sbr_cell_26_66:
    mov edi, ecx
__sbr_cell_26_66_end:
__sbr_cell_26_67:
    shr edi, 3
__sbr_cell_26_67_end:
__sbr_cell_26_68:
    xor r8d, r8d
__sbr_cell_26_68_end:
__sbr_cell_26_69:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_69_end:
__sbr_cell_26_70:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_70_end:
__sbr_cell_26_71:
    setl r8b
__sbr_cell_26_71_end:
__sbr_cell_26_72:
    add r8d, ecx
__sbr_cell_26_72_end:
__sbr_cell_26_73:
    movzx edi, BYTE PTR [r9+rdi*1+0]
__sbr_cell_26_73_end:
__sbr_cell_26_74:
    and cl, 7
__sbr_cell_26_74_end:
__sbr_cell_26_75:
    shl edi, cl
__sbr_cell_26_75_end:
__sbr_cell_26_76:
    mov DWORD PTR [rsi+8], r8d
__sbr_cell_26_76_end:
__sbr_cell_26_77:
    shr dil, 7
__sbr_cell_26_77_end:
__sbr_cell_26_78:
    mov BYTE PTR [rdx+rax*1+29], dil
__sbr_cell_26_78_end:
read_sbr_dtdf.L5272:
__sbr_cell_26_79:
    mov BYTE PTR [rdx+37], 0
__sbr_cell_26_79_end:
__sbr_cell_26_80:
    mov eax, DWORD PTR [rdx+24]
__sbr_cell_26_80_end:
__sbr_cell_26_81:
    dec eax
__sbr_cell_26_81_end:
__sbr_cell_26_82:
    test eax, eax
__sbr_cell_26_82_end:
__sbr_cell_26_83:
    jle read_sbr_dtdf.L5622
__sbr_cell_26_83_end:
__sbr_cell_26_84:
    cmp eax, 1
__sbr_cell_26_84_end:
__sbr_cell_26_85:
    jne read_sbr_dtdf.L528f
__sbr_cell_26_85_end:
__sbr_cell_26_86:
    xor eax, eax
__sbr_cell_26_86_end:
__sbr_cell_26_87:
    jmp read_sbr_dtdf.L5317
__sbr_cell_26_87_end:
read_sbr_dtdf.L528f:
__sbr_cell_26_88:
    mov edi, eax
__sbr_cell_26_88_end:
__sbr_cell_26_89:
    mov r8d, edi
__sbr_cell_26_89_end:
__sbr_cell_26_90:
    and r8d, 2147483646
__sbr_cell_26_90_end:
__sbr_cell_26_91:
    xor eax, eax
__sbr_cell_26_91_end:
__sbr_cell_26_92:
    .nops 1
__sbr_cell_26_92_end:
read_sbr_dtdf.L52a0:
__sbr_cell_26_93:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_93_end:
__sbr_cell_26_94:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_94_end:
__sbr_cell_26_95:
    mov r10d, ecx
__sbr_cell_26_95_end:
__sbr_cell_26_96:
    shr r10d, 3
__sbr_cell_26_96_end:
__sbr_cell_26_97:
    xor r11d, r11d
__sbr_cell_26_97_end:
__sbr_cell_26_98:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_98_end:
__sbr_cell_26_99:
    setl r11b
__sbr_cell_26_99_end:
__sbr_cell_26_100:
    add r11d, ecx
__sbr_cell_26_100_end:
__sbr_cell_26_101:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_101_end:
__sbr_cell_26_102:
    and cl, 7
__sbr_cell_26_102_end:
__sbr_cell_26_103:
    shl r9d, cl
__sbr_cell_26_103_end:
__sbr_cell_26_104:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_104_end:
__sbr_cell_26_105:
    shr r9b, 7
__sbr_cell_26_105_end:
__sbr_cell_26_106:
    mov BYTE PTR [rdx+rax*1+38], r9b
__sbr_cell_26_106_end:
read_sbr_dtdf.L52d2:
__sbr_cell_26_107:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_107_end:
__sbr_cell_26_108:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_108_end:
__sbr_cell_26_109:
    mov r10d, ecx
__sbr_cell_26_109_end:
__sbr_cell_26_110:
    shr r10d, 3
__sbr_cell_26_110_end:
__sbr_cell_26_111:
    xor r11d, r11d
__sbr_cell_26_111_end:
__sbr_cell_26_112:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_112_end:
__sbr_cell_26_113:
    setl r11b
__sbr_cell_26_113_end:
__sbr_cell_26_114:
    add r11d, ecx
__sbr_cell_26_114_end:
__sbr_cell_26_115:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_115_end:
__sbr_cell_26_116:
    and cl, 7
__sbr_cell_26_116_end:
__sbr_cell_26_117:
    shl r9d, cl
__sbr_cell_26_117_end:
__sbr_cell_26_118:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_118_end:
__sbr_cell_26_119:
    shr r9b, 7
__sbr_cell_26_119_end:
__sbr_cell_26_120:
    mov BYTE PTR [rdx+rax*1+39], r9b
__sbr_cell_26_120_end:
__sbr_cell_26_121:
    add rax, 2
__sbr_cell_26_121_end:
__sbr_cell_26_122:
    cmp r8, rax
__sbr_cell_26_122_end:
__sbr_cell_26_123:
    jne read_sbr_dtdf.L52a0
__sbr_cell_26_123_end:
__sbr_cell_26_124:
    test dil, 1
__sbr_cell_26_124_end:
__sbr_cell_26_125:
    je read_sbr_dtdf.L5622
__sbr_cell_26_125_end:
read_sbr_dtdf.L5317:
__sbr_cell_26_126:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_126_end:
__sbr_cell_26_127:
    mov edi, ecx
__sbr_cell_26_127_end:
__sbr_cell_26_128:
    shr edi, 3
__sbr_cell_26_128_end:
__sbr_cell_26_129:
    xor r8d, r8d
__sbr_cell_26_129_end:
__sbr_cell_26_130:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_130_end:
__sbr_cell_26_131:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_131_end:
__sbr_cell_26_132:
    setl r8b
__sbr_cell_26_132_end:
__sbr_cell_26_133:
    add r8d, ecx
__sbr_cell_26_133_end:
__sbr_cell_26_134:
    movzx edi, BYTE PTR [r9+rdi*1+0]
__sbr_cell_26_134_end:
__sbr_cell_26_135:
    and cl, 7
__sbr_cell_26_135_end:
__sbr_cell_26_136:
    shl edi, cl
__sbr_cell_26_136_end:
__sbr_cell_26_137:
    mov DWORD PTR [rsi+8], r8d
__sbr_cell_26_137_end:
__sbr_cell_26_138:
    shr dil, 7
__sbr_cell_26_138_end:
__sbr_cell_26_139:
    mov BYTE PTR [rdx+rax*1+38], dil
__sbr_cell_26_139_end:
read_sbr_dtdf.done:
__sbr_cell_26_140:
    ret
__sbr_cell_26_140_end:
read_sbr_dtdf.L5347:
__sbr_cell_26_141:
    mov r8d, edi
__sbr_cell_26_141_end:
__sbr_cell_26_142:
    and r8d, 2147483646
__sbr_cell_26_142_end:
__sbr_cell_26_143:
    xor eax, eax
__sbr_cell_26_143_end:
__sbr_cell_26_144:
    .nops 1
__sbr_cell_26_144_end:
read_sbr_dtdf.L5360:
__sbr_cell_26_145:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_145_end:
__sbr_cell_26_146:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_146_end:
__sbr_cell_26_147:
    mov r10d, ecx
__sbr_cell_26_147_end:
__sbr_cell_26_148:
    shr r10d, 3
__sbr_cell_26_148_end:
__sbr_cell_26_149:
    xor r11d, r11d
__sbr_cell_26_149_end:
__sbr_cell_26_150:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_150_end:
__sbr_cell_26_151:
    setl r11b
__sbr_cell_26_151_end:
__sbr_cell_26_152:
    add r11d, ecx
__sbr_cell_26_152_end:
__sbr_cell_26_153:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_153_end:
__sbr_cell_26_154:
    and cl, 7
__sbr_cell_26_154_end:
__sbr_cell_26_155:
    shl r9d, cl
__sbr_cell_26_155_end:
__sbr_cell_26_156:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_156_end:
__sbr_cell_26_157:
    shr r9b, 7
__sbr_cell_26_157_end:
__sbr_cell_26_158:
    mov BYTE PTR [rdx+rax*1+28], r9b
__sbr_cell_26_158_end:
read_sbr_dtdf.L5392:
__sbr_cell_26_159:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_159_end:
__sbr_cell_26_160:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_160_end:
__sbr_cell_26_161:
    mov r10d, ecx
__sbr_cell_26_161_end:
__sbr_cell_26_162:
    shr r10d, 3
__sbr_cell_26_162_end:
__sbr_cell_26_163:
    xor r11d, r11d
__sbr_cell_26_163_end:
__sbr_cell_26_164:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_164_end:
__sbr_cell_26_165:
    setl r11b
__sbr_cell_26_165_end:
__sbr_cell_26_166:
    add r11d, ecx
__sbr_cell_26_166_end:
__sbr_cell_26_167:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_167_end:
__sbr_cell_26_168:
    and cl, 7
__sbr_cell_26_168_end:
__sbr_cell_26_169:
    shl r9d, cl
__sbr_cell_26_169_end:
__sbr_cell_26_170:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_170_end:
__sbr_cell_26_171:
    shr r9b, 7
__sbr_cell_26_171_end:
__sbr_cell_26_172:
    mov BYTE PTR [rdx+rax*1+29], r9b
__sbr_cell_26_172_end:
__sbr_cell_26_173:
    add rax, 2
__sbr_cell_26_173_end:
__sbr_cell_26_174:
    cmp r8, rax
__sbr_cell_26_174_end:
__sbr_cell_26_175:
    jne read_sbr_dtdf.L5360
__sbr_cell_26_175_end:
__sbr_cell_26_176:
    test dil, 1
__sbr_cell_26_176_end:
__sbr_cell_26_177:
    je read_sbr_dtdf.L5402
__sbr_cell_26_177_end:
read_sbr_dtdf.L53d3:
__sbr_cell_26_178:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_178_end:
__sbr_cell_26_179:
    mov edi, ecx
__sbr_cell_26_179_end:
__sbr_cell_26_180:
    shr edi, 3
__sbr_cell_26_180_end:
__sbr_cell_26_181:
    xor r8d, r8d
__sbr_cell_26_181_end:
__sbr_cell_26_182:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_182_end:
__sbr_cell_26_183:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_183_end:
__sbr_cell_26_184:
    setl r8b
__sbr_cell_26_184_end:
__sbr_cell_26_185:
    add r8d, ecx
__sbr_cell_26_185_end:
__sbr_cell_26_186:
    movzx edi, BYTE PTR [r9+rdi*1+0]
__sbr_cell_26_186_end:
__sbr_cell_26_187:
    and cl, 7
__sbr_cell_26_187_end:
__sbr_cell_26_188:
    shl edi, cl
__sbr_cell_26_188_end:
__sbr_cell_26_189:
    mov DWORD PTR [rsi+8], r8d
__sbr_cell_26_189_end:
__sbr_cell_26_190:
    shr dil, 7
__sbr_cell_26_190_end:
__sbr_cell_26_191:
    mov BYTE PTR [rdx+rax*1+28], dil
__sbr_cell_26_191_end:
read_sbr_dtdf.L5402:
__sbr_cell_26_192:
    movsxd rdi, DWORD PTR [rdx+24]
__sbr_cell_26_192_end:
__sbr_cell_26_193:
    test rdi, rdi
__sbr_cell_26_193_end:
__sbr_cell_26_194:
    jle read_sbr_dtdf.L5622
__sbr_cell_26_194_end:
__sbr_cell_26_195:
    cmp edi, 1
__sbr_cell_26_195_end:
__sbr_cell_26_196:
    je read_sbr_dtdf.L5564
__sbr_cell_26_196_end:
__sbr_cell_26_197:
    mov r8d, edi
__sbr_cell_26_197_end:
__sbr_cell_26_198:
    and r8d, 2147483646
__sbr_cell_26_198_end:
__sbr_cell_26_199:
    xor eax, eax
__sbr_cell_26_199_end:
__sbr_cell_26_200:
    .nops 1
__sbr_cell_26_200_end:
read_sbr_dtdf.L5430:
__sbr_cell_26_201:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_201_end:
__sbr_cell_26_202:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_202_end:
__sbr_cell_26_203:
    mov r10d, ecx
__sbr_cell_26_203_end:
__sbr_cell_26_204:
    shr r10d, 3
__sbr_cell_26_204_end:
__sbr_cell_26_205:
    xor r11d, r11d
__sbr_cell_26_205_end:
__sbr_cell_26_206:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_206_end:
__sbr_cell_26_207:
    setl r11b
__sbr_cell_26_207_end:
__sbr_cell_26_208:
    add r11d, ecx
__sbr_cell_26_208_end:
__sbr_cell_26_209:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_209_end:
__sbr_cell_26_210:
    and cl, 7
__sbr_cell_26_210_end:
__sbr_cell_26_211:
    shl r9d, cl
__sbr_cell_26_211_end:
__sbr_cell_26_212:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_212_end:
__sbr_cell_26_213:
    shr r9b, 7
__sbr_cell_26_213_end:
__sbr_cell_26_214:
    mov BYTE PTR [rdx+rax*1+37], r9b
__sbr_cell_26_214_end:
read_sbr_dtdf.L5462:
__sbr_cell_26_215:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_215_end:
__sbr_cell_26_216:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_216_end:
__sbr_cell_26_217:
    mov r10d, ecx
__sbr_cell_26_217_end:
__sbr_cell_26_218:
    shr r10d, 3
__sbr_cell_26_218_end:
__sbr_cell_26_219:
    xor r11d, r11d
__sbr_cell_26_219_end:
__sbr_cell_26_220:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_220_end:
__sbr_cell_26_221:
    setl r11b
__sbr_cell_26_221_end:
__sbr_cell_26_222:
    add r11d, ecx
__sbr_cell_26_222_end:
__sbr_cell_26_223:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_223_end:
__sbr_cell_26_224:
    and cl, 7
__sbr_cell_26_224_end:
__sbr_cell_26_225:
    shl r9d, cl
__sbr_cell_26_225_end:
__sbr_cell_26_226:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_226_end:
__sbr_cell_26_227:
    shr r9b, 7
__sbr_cell_26_227_end:
__sbr_cell_26_228:
    mov BYTE PTR [rdx+rax*1+38], r9b
__sbr_cell_26_228_end:
__sbr_cell_26_229:
    add rax, 2
__sbr_cell_26_229_end:
__sbr_cell_26_230:
    cmp r8, rax
__sbr_cell_26_230_end:
__sbr_cell_26_231:
    jne read_sbr_dtdf.L5430
__sbr_cell_26_231_end:
__sbr_cell_26_232:
    jmp read_sbr_dtdf.L55ed
__sbr_cell_26_232_end:
read_sbr_dtdf.L54a2:
__sbr_cell_26_233:
    mov r8d, edi
__sbr_cell_26_233_end:
__sbr_cell_26_234:
    and r8d, 2147483646
__sbr_cell_26_234_end:
__sbr_cell_26_235:
    xor eax, eax
__sbr_cell_26_235_end:
__sbr_cell_26_236:
    .nops 1
__sbr_cell_26_236_end:
read_sbr_dtdf.L54b0:
__sbr_cell_26_237:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_237_end:
__sbr_cell_26_238:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_238_end:
__sbr_cell_26_239:
    mov r10d, ecx
__sbr_cell_26_239_end:
__sbr_cell_26_240:
    shr r10d, 3
__sbr_cell_26_240_end:
__sbr_cell_26_241:
    xor r11d, r11d
__sbr_cell_26_241_end:
__sbr_cell_26_242:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_242_end:
__sbr_cell_26_243:
    setl r11b
__sbr_cell_26_243_end:
__sbr_cell_26_244:
    add r11d, ecx
__sbr_cell_26_244_end:
__sbr_cell_26_245:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_245_end:
__sbr_cell_26_246:
    and cl, 7
__sbr_cell_26_246_end:
__sbr_cell_26_247:
    shl r9d, cl
__sbr_cell_26_247_end:
__sbr_cell_26_248:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_248_end:
__sbr_cell_26_249:
    shr r9b, 7
__sbr_cell_26_249_end:
__sbr_cell_26_250:
    mov BYTE PTR [rdx+rax*1+28], r9b
__sbr_cell_26_250_end:
read_sbr_dtdf.L54e2:
__sbr_cell_26_251:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_251_end:
__sbr_cell_26_252:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_252_end:
__sbr_cell_26_253:
    mov r10d, ecx
__sbr_cell_26_253_end:
__sbr_cell_26_254:
    shr r10d, 3
__sbr_cell_26_254_end:
__sbr_cell_26_255:
    xor r11d, r11d
__sbr_cell_26_255_end:
__sbr_cell_26_256:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_256_end:
__sbr_cell_26_257:
    setl r11b
__sbr_cell_26_257_end:
__sbr_cell_26_258:
    add r11d, ecx
__sbr_cell_26_258_end:
__sbr_cell_26_259:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_259_end:
__sbr_cell_26_260:
    and cl, 7
__sbr_cell_26_260_end:
__sbr_cell_26_261:
    shl r9d, cl
__sbr_cell_26_261_end:
__sbr_cell_26_262:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_262_end:
__sbr_cell_26_263:
    shr r9b, 7
__sbr_cell_26_263_end:
__sbr_cell_26_264:
    mov BYTE PTR [rdx+rax*1+29], r9b
__sbr_cell_26_264_end:
__sbr_cell_26_265:
    add rax, 2
__sbr_cell_26_265_end:
__sbr_cell_26_266:
    cmp r8, rax
__sbr_cell_26_266_end:
__sbr_cell_26_267:
    jne read_sbr_dtdf.L54b0
__sbr_cell_26_267_end:
__sbr_cell_26_268:
    test dil, 1
__sbr_cell_26_268_end:
__sbr_cell_26_269:
    je read_sbr_dtdf.L5552
__sbr_cell_26_269_end:
read_sbr_dtdf.L5523:
__sbr_cell_26_270:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_270_end:
__sbr_cell_26_271:
    mov edi, ecx
__sbr_cell_26_271_end:
__sbr_cell_26_272:
    shr edi, 3
__sbr_cell_26_272_end:
__sbr_cell_26_273:
    xor r8d, r8d
__sbr_cell_26_273_end:
__sbr_cell_26_274:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_274_end:
__sbr_cell_26_275:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_275_end:
__sbr_cell_26_276:
    setl r8b
__sbr_cell_26_276_end:
__sbr_cell_26_277:
    add r8d, ecx
__sbr_cell_26_277_end:
__sbr_cell_26_278:
    movzx edi, BYTE PTR [r9+rdi*1+0]
__sbr_cell_26_278_end:
__sbr_cell_26_279:
    and cl, 7
__sbr_cell_26_279_end:
__sbr_cell_26_280:
    shl edi, cl
__sbr_cell_26_280_end:
__sbr_cell_26_281:
    mov DWORD PTR [rsi+8], r8d
__sbr_cell_26_281_end:
__sbr_cell_26_282:
    shr dil, 7
__sbr_cell_26_282_end:
__sbr_cell_26_283:
    mov BYTE PTR [rdx+rax*1+28], dil
__sbr_cell_26_283_end:
read_sbr_dtdf.L5552:
__sbr_cell_26_284:
    movsxd rdi, DWORD PTR [rdx+24]
__sbr_cell_26_284_end:
__sbr_cell_26_285:
    test rdi, rdi
__sbr_cell_26_285_end:
__sbr_cell_26_286:
    jle read_sbr_dtdf.L5622
__sbr_cell_26_286_end:
__sbr_cell_26_287:
    cmp edi, 1
__sbr_cell_26_287_end:
__sbr_cell_26_288:
    jne read_sbr_dtdf.L556b
__sbr_cell_26_288_end:
read_sbr_dtdf.L5564:
__sbr_cell_26_289:
    xor eax, eax
__sbr_cell_26_289_end:
__sbr_cell_26_290:
    jmp read_sbr_dtdf.L55f3
__sbr_cell_26_290_end:
read_sbr_dtdf.L556b:
__sbr_cell_26_291:
    mov r8d, edi
__sbr_cell_26_291_end:
__sbr_cell_26_292:
    and r8d, 2147483646
__sbr_cell_26_292_end:
__sbr_cell_26_293:
    xor eax, eax
__sbr_cell_26_293_end:
__sbr_cell_26_294:
    .nops 1
__sbr_cell_26_294_end:
read_sbr_dtdf.L5580:
__sbr_cell_26_295:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_295_end:
__sbr_cell_26_296:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_296_end:
__sbr_cell_26_297:
    mov r10d, ecx
__sbr_cell_26_297_end:
__sbr_cell_26_298:
    shr r10d, 3
__sbr_cell_26_298_end:
__sbr_cell_26_299:
    xor r11d, r11d
__sbr_cell_26_299_end:
__sbr_cell_26_300:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_300_end:
__sbr_cell_26_301:
    setl r11b
__sbr_cell_26_301_end:
__sbr_cell_26_302:
    add r11d, ecx
__sbr_cell_26_302_end:
__sbr_cell_26_303:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_303_end:
__sbr_cell_26_304:
    and cl, 7
__sbr_cell_26_304_end:
__sbr_cell_26_305:
    shl r9d, cl
__sbr_cell_26_305_end:
__sbr_cell_26_306:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_306_end:
__sbr_cell_26_307:
    shr r9b, 7
__sbr_cell_26_307_end:
__sbr_cell_26_308:
    mov BYTE PTR [rdx+rax*1+37], r9b
__sbr_cell_26_308_end:
read_sbr_dtdf.L55b2:
__sbr_cell_26_309:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_309_end:
__sbr_cell_26_310:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_310_end:
__sbr_cell_26_311:
    mov r10d, ecx
__sbr_cell_26_311_end:
__sbr_cell_26_312:
    shr r10d, 3
__sbr_cell_26_312_end:
__sbr_cell_26_313:
    xor r11d, r11d
__sbr_cell_26_313_end:
__sbr_cell_26_314:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_314_end:
__sbr_cell_26_315:
    setl r11b
__sbr_cell_26_315_end:
__sbr_cell_26_316:
    add r11d, ecx
__sbr_cell_26_316_end:
__sbr_cell_26_317:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_26_317_end:
__sbr_cell_26_318:
    and cl, 7
__sbr_cell_26_318_end:
__sbr_cell_26_319:
    shl r9d, cl
__sbr_cell_26_319_end:
__sbr_cell_26_320:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_26_320_end:
__sbr_cell_26_321:
    shr r9b, 7
__sbr_cell_26_321_end:
__sbr_cell_26_322:
    mov BYTE PTR [rdx+rax*1+38], r9b
__sbr_cell_26_322_end:
__sbr_cell_26_323:
    add rax, 2
__sbr_cell_26_323_end:
__sbr_cell_26_324:
    cmp r8, rax
__sbr_cell_26_324_end:
__sbr_cell_26_325:
    jne read_sbr_dtdf.L5580
__sbr_cell_26_325_end:
read_sbr_dtdf.L55ed:
__sbr_cell_26_326:
    test dil, 1
__sbr_cell_26_326_end:
__sbr_cell_26_327:
    je read_sbr_dtdf.L5622
__sbr_cell_26_327_end:
read_sbr_dtdf.L55f3:
__sbr_cell_26_328:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_26_328_end:
__sbr_cell_26_329:
    mov edi, ecx
__sbr_cell_26_329_end:
__sbr_cell_26_330:
    shr edi, 3
__sbr_cell_26_330_end:
__sbr_cell_26_331:
    xor r8d, r8d
__sbr_cell_26_331_end:
__sbr_cell_26_332:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_26_332_end:
__sbr_cell_26_333:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_26_333_end:
__sbr_cell_26_334:
    setl r8b
__sbr_cell_26_334_end:
__sbr_cell_26_335:
    add r8d, ecx
__sbr_cell_26_335_end:
__sbr_cell_26_336:
    movzx edi, BYTE PTR [r9+rdi*1+0]
__sbr_cell_26_336_end:
__sbr_cell_26_337:
    and cl, 7
__sbr_cell_26_337_end:
__sbr_cell_26_338:
    shl edi, cl
__sbr_cell_26_338_end:
__sbr_cell_26_339:
    mov DWORD PTR [rsi+8], r8d
__sbr_cell_26_339_end:
__sbr_cell_26_340:
    shr dil, 7
__sbr_cell_26_340_end:
__sbr_cell_26_341:
    mov BYTE PTR [rdx+rax*1+37], dil
__sbr_cell_26_341_end:
read_sbr_dtdf.L5622:
__sbr_cell_26_342:
    jmp read_sbr_dtdf.done
__sbr_cell_26_342_end:
__sbr_cell_26_343:
    int3
__sbr_cell_26_343_end:
__sbr_cell_26_344:
    int3
__sbr_cell_26_344_end:
__sbr_cell_26_345:
    int3
__sbr_cell_26_345_end:
__sbr_cell_26_346:
    int3
__sbr_cell_26_346_end:
__sbr_cell_26_347:
    int3
__sbr_cell_26_347_end:
__sbr_cell_26_348:
    int3
__sbr_cell_26_348_end:
__sbr_cell_26_349:
    int3
__sbr_cell_26_349_end:
__sbr_cell_26_350:
    int3
__sbr_cell_26_350_end:
__sbr_cell_26_351:
    int3
__sbr_cell_26_351_end:
__sbr_cell_26_352:
    int3
__sbr_cell_26_352_end:
__sbr_cell_26_353:
    int3
__sbr_cell_26_353_end:
__sbr_cell_26_354:
    int3
__sbr_cell_26_354_end:
__sbr_cell_26_355:
    int3
__sbr_cell_26_355_end:
.size read_sbr_dtdf, .-read_sbr_dtdf
.section .text.read_sbr_envelope,"ax",@progbits
.globl read_sbr_envelope
.type read_sbr_envelope,@function
read_sbr_envelope:
__sbr_cell_27_0:
    push rbp
__sbr_cell_27_0_end:
__sbr_cell_27_1:
    mov rbp, rsp
__sbr_cell_27_1_end:
__sbr_cell_27_2:
    push r15
__sbr_cell_27_2_end:
__sbr_cell_27_3:
    push r14
__sbr_cell_27_3_end:
__sbr_cell_27_4:
    push r13
__sbr_cell_27_4_end:
__sbr_cell_27_5:
    push r12
__sbr_cell_27_5_end:
__sbr_cell_27_6:
    push rbx
__sbr_cell_27_6_end:
__sbr_cell_27_7:
    sub rsp, 120
__sbr_cell_27_7_end:
read_sbr_envelope.L57c1:
__sbr_cell_27_8:
    mov r15, rcx
__sbr_cell_27_8_end:
__sbr_cell_27_9:
    test r8d, r8d
__sbr_cell_27_9_end:
__sbr_cell_27_10:
    je read_sbr_envelope.L5834
__sbr_cell_27_10_end:
read_sbr_envelope.L57c9:
__sbr_cell_27_11:
    mov ecx, DWORD PTR [rsi+60]
__sbr_cell_27_11_end:
__sbr_cell_27_12:
    xor r11d, r11d
__sbr_cell_27_12_end:
__sbr_cell_27_13:
    cmp ecx, 1
__sbr_cell_27_13_end:
__sbr_cell_27_14:
    sete r11b
__sbr_cell_27_14_end:
__sbr_cell_27_15:
    inc r11d
__sbr_cell_27_15_end:
__sbr_cell_27_16:
    lea r12, [rsi+311776]
__sbr_cell_27_16_end:
__sbr_cell_27_17:
    mov r14d, DWORD PTR [rsi+311780]
__sbr_cell_27_17_end:
__sbr_cell_27_18:
    and r14d, 1
__sbr_cell_27_18_end:
__sbr_cell_27_19:
    test ecx, ecx
__sbr_cell_27_19_end:
__sbr_cell_27_20:
    je read_sbr_envelope.L584c
__sbr_cell_27_20_end:
read_sbr_envelope.L57ef:
__sbr_cell_27_21:
    xor r10d, r10d
__sbr_cell_27_21_end:
__sbr_cell_27_22:
    xor r9d, r9d
__sbr_cell_27_22_end:
__sbr_cell_27_23:
    cmp DWORD PTR [r15+100], 0
__sbr_cell_27_23_end:
__sbr_cell_27_24:
    sete r10b
__sbr_cell_27_24_end:
__sbr_cell_27_25:
    setne r9b
__sbr_cell_27_25_end:
__sbr_cell_27_26:
    lea r8, [rip+ff_aac_sbr_vlc]
__sbr_cell_27_26_end:
__sbr_cell_27_27:
    shl r9d, 5
__sbr_cell_27_27_end:
__sbr_cell_27_28:
    lea rcx, [r9+r8*1+0]
__sbr_cell_27_28_end:
__sbr_cell_27_29:
    add rcx, 16
__sbr_cell_27_29_end:
__sbr_cell_27_30:
    add r9, r8
__sbr_cell_27_30_end:
__sbr_cell_27_31:
    add r9, 24
__sbr_cell_27_31_end:
__sbr_cell_27_32:
    add r10d, 5
__sbr_cell_27_32_end:
__sbr_cell_27_33:
    xor eax, eax
__sbr_cell_27_33_end:
__sbr_cell_27_34:
    cmp DWORD PTR [r15+8], 0
__sbr_cell_27_34_end:
__sbr_cell_27_35:
    mov r8d, 0
__sbr_cell_27_35_end:
__sbr_cell_27_36:
    jne read_sbr_envelope.L5893
__sbr_cell_27_36_end:
__sbr_cell_27_37:
    jmp read_sbr_envelope.L6075
__sbr_cell_27_37_end:
read_sbr_envelope.L5834:
__sbr_cell_27_38:
    lea r12, [rsi+311776]
__sbr_cell_27_38_end:
__sbr_cell_27_39:
    mov r14d, DWORD PTR [rsi+311780]
__sbr_cell_27_39_end:
__sbr_cell_27_40:
    and r14d, 1
__sbr_cell_27_40_end:
__sbr_cell_27_41:
    mov r11d, 1
__sbr_cell_27_41_end:
read_sbr_envelope.L584c:
__sbr_cell_27_42:
    xor r10d, r10d
__sbr_cell_27_42_end:
__sbr_cell_27_43:
    xor r9d, r9d
__sbr_cell_27_43_end:
__sbr_cell_27_44:
    cmp DWORD PTR [r15+100], 0
__sbr_cell_27_44_end:
__sbr_cell_27_45:
    sete r10b
__sbr_cell_27_45_end:
__sbr_cell_27_46:
    lea r8, [rip+ff_aac_sbr_vlc]
__sbr_cell_27_46_end:
__sbr_cell_27_47:
    lea rcx, [rip+(ff_aac_sbr_vlc + 32)]
__sbr_cell_27_47_end:
__sbr_cell_27_48:
    cmove rcx, r8
__sbr_cell_27_48_end:
__sbr_cell_27_49:
    setne r9b
__sbr_cell_27_49_end:
__sbr_cell_27_50:
    shl r9d, 5
__sbr_cell_27_50_end:
__sbr_cell_27_51:
    add r9, r8
__sbr_cell_27_51_end:
__sbr_cell_27_52:
    add r9, 8
__sbr_cell_27_52_end:
__sbr_cell_27_53:
    or r10d, 6
__sbr_cell_27_53_end:
__sbr_cell_27_54:
    xor eax, eax
__sbr_cell_27_54_end:
__sbr_cell_27_55:
    cmp DWORD PTR [r15+8], 0
__sbr_cell_27_55_end:
__sbr_cell_27_56:
    mov r8d, 0
__sbr_cell_27_56_end:
__sbr_cell_27_57:
    je read_sbr_envelope.L6075
__sbr_cell_27_57_end:
read_sbr_envelope.L5893:
__sbr_cell_27_58:
    mov QWORD PTR [rbp-80], rdi
__sbr_cell_27_58_end:
__sbr_cell_27_59:
    mov rax, QWORD PTR [r9+0]
__sbr_cell_27_59_end:
__sbr_cell_27_60:
    mov QWORD PTR [rbp-152], rax
__sbr_cell_27_60_end:
__sbr_cell_27_61:
    mov r13, QWORD PTR [rcx+0]
__sbr_cell_27_61_end:
read_sbr_envelope.L58a4:
__sbr_cell_27_62:
    mov eax, r10d
__sbr_cell_27_62_end:
__sbr_cell_27_63:
    neg al
__sbr_cell_27_63_end:
__sbr_cell_27_64:
    mov BYTE PTR [rbp-45], al
__sbr_cell_27_64_end:
__sbr_cell_27_65:
    mov eax, 96
__sbr_cell_27_65_end:
__sbr_cell_27_66:
    sub eax, r14d
__sbr_cell_27_66_end:
__sbr_cell_27_67:
    mov QWORD PTR [rbp-144], rax
__sbr_cell_27_67_end:
__sbr_cell_27_68:
    mov eax, r14d
__sbr_cell_27_68_end:
__sbr_cell_27_69:
    mov QWORD PTR [rbp-136], rax
__sbr_cell_27_69_end:
read_sbr_envelope.L58c5:
__sbr_cell_27_70:
    lea rax, [r15+86544]
__sbr_cell_27_70_end:
__sbr_cell_27_71:
    mov QWORD PTR [rbp-88], rax
__sbr_cell_27_71_end:
__sbr_cell_27_72:
    mov eax, 2
__sbr_cell_27_72_end:
__sbr_cell_27_73:
    sub eax, r14d
__sbr_cell_27_73_end:
__sbr_cell_27_74:
    mov DWORD PTR [rbp-108], eax
__sbr_cell_27_74_end:
__sbr_cell_27_75:
    lea rax, [r15+86545]
__sbr_cell_27_75_end:
__sbr_cell_27_76:
    mov QWORD PTR [rbp-96], rax
__sbr_cell_27_76_end:
read_sbr_envelope.L58e6:
__sbr_cell_27_77:
    xor r9d, r9d
__sbr_cell_27_77_end:
__sbr_cell_27_78:
    mov QWORD PTR [rbp-120], rsi
__sbr_cell_27_78_end:
__sbr_cell_27_79:
    mov DWORD PTR [rbp-44], r11d
__sbr_cell_27_79_end:
read_sbr_envelope.L58f1:
__sbr_cell_27_80:
    mov QWORD PTR [rbp-64], r12
__sbr_cell_27_80_end:
__sbr_cell_27_81:
    mov DWORD PTR [rbp-112], r10d
__sbr_cell_27_81_end:
__sbr_cell_27_82:
    mov QWORD PTR [rbp-56], r15
__sbr_cell_27_82_end:
read_sbr_envelope.L58fd:
__sbr_cell_27_83:
    cmp BYTE PTR [r15+r9*1+28], 0
__sbr_cell_27_83_end:
__sbr_cell_27_84:
    mov QWORD PTR [rbp-104], r9
__sbr_cell_27_84_end:
__sbr_cell_27_85:
    je read_sbr_envelope.L5a60
__sbr_cell_27_85_end:
read_sbr_envelope.L590d:
__sbr_cell_27_86:
    cmp r9, 8
__sbr_cell_27_86_end:
__sbr_cell_27_87:
    je read_sbr_envelope.L60ea
__sbr_cell_27_87_end:
__sbr_cell_27_88:
    lea rax, [r9+1]
__sbr_cell_27_88_end:
__sbr_cell_27_89:
    mov QWORD PTR [rbp-72], rax
__sbr_cell_27_89_end:
__sbr_cell_27_90:
    movzx eax, BYTE PTR [r15+r9*1+13]
__sbr_cell_27_90_end:
__sbr_cell_27_91:
    cmp al, BYTE PTR [r15+r9*1+12]
__sbr_cell_27_91_end:
__sbr_cell_27_92:
    jne read_sbr_envelope.L5be0
__sbr_cell_27_92_end:
read_sbr_envelope.L5930:
__sbr_cell_27_93:
    cmp al, 1
__sbr_cell_27_93_end:
__sbr_cell_27_94:
    ja read_sbr_envelope.L60bd
__sbr_cell_27_94_end:
__sbr_cell_27_95:
    xor esi, esi
__sbr_cell_27_95_end:
__sbr_cell_27_96:
    .nops 1
__sbr_cell_27_96_end:
read_sbr_envelope.L5940:
__sbr_cell_27_97:
    movzx eax, al
__sbr_cell_27_97_end:
__sbr_cell_27_98:
    mov eax, DWORD PTR [r12+rax*4+0]
__sbr_cell_27_98_end:
__sbr_cell_27_99:
    cmp rsi, rax
__sbr_cell_27_99_end:
__sbr_cell_27_100:
    jae read_sbr_envelope.L5f90
__sbr_cell_27_100_end:
__sbr_cell_27_101:
    cmp rsi, 48
__sbr_cell_27_101_end:
__sbr_cell_27_102:
    je read_sbr_envelope.L60cc
__sbr_cell_27_102_end:
read_sbr_envelope.L595a:
__sbr_cell_27_103:
    mov rax, QWORD PTR [rbp-88]
__sbr_cell_27_103_end:
__sbr_cell_27_104:
    movzx r9d, BYTE PTR [rax+rsi*1-48]
__sbr_cell_27_104_end:
__sbr_cell_27_105:
    mov r14d, DWORD PTR [rdx+8]
__sbr_cell_27_105_end:
__sbr_cell_27_106:
    mov edi, DWORD PTR [rdx+16]
__sbr_cell_27_106_end:
__sbr_cell_27_107:
    mov r8, QWORD PTR [rdx+0]
__sbr_cell_27_107_end:
__sbr_cell_27_108:
    mov eax, r14d
__sbr_cell_27_108_end:
__sbr_cell_27_109:
    shr eax, 3
__sbr_cell_27_109_end:
__sbr_cell_27_110:
    mov eax, DWORD PTR [r8+rax*1+0]
__sbr_cell_27_110_end:
__sbr_cell_27_111:
    bswap eax
__sbr_cell_27_111_end:
__sbr_cell_27_112:
    mov ecx, r14d
__sbr_cell_27_112_end:
__sbr_cell_27_113:
    and cl, 7
__sbr_cell_27_113_end:
__sbr_cell_27_114:
    shl eax, cl
__sbr_cell_27_114_end:
__sbr_cell_27_115:
    shr eax, 23
__sbr_cell_27_115_end:
__sbr_cell_27_116:
    mov ecx, eax
__sbr_cell_27_116_end:
__sbr_cell_27_117:
    movsx eax, WORD PTR [r13+rcx*4+0]
__sbr_cell_27_117_end:
__sbr_cell_27_118:
    movsx r10d, WORD PTR [r13+rcx*4+2]
__sbr_cell_27_118_end:
__sbr_cell_27_119:
    test r10d, r10d
__sbr_cell_27_119_end:
__sbr_cell_27_120:
    jns read_sbr_envelope.L5a11
__sbr_cell_27_120_end:
read_sbr_envelope.L5998:
__sbr_cell_27_121:
    add r14d, 9
__sbr_cell_27_121_end:
__sbr_cell_27_122:
    cmp edi, r14d
__sbr_cell_27_122_end:
__sbr_cell_27_123:
    cmovb r14d, edi
__sbr_cell_27_123_end:
__sbr_cell_27_124:
    mov ecx, r14d
__sbr_cell_27_124_end:
__sbr_cell_27_125:
    shr ecx, 3
__sbr_cell_27_125_end:
__sbr_cell_27_126:
    mov r11d, DWORD PTR [r8+rcx*1+0]
__sbr_cell_27_126_end:
__sbr_cell_27_127:
    bswap r11d
__sbr_cell_27_127_end:
__sbr_cell_27_128:
    mov ecx, r14d
__sbr_cell_27_128_end:
__sbr_cell_27_129:
    and cl, 7
__sbr_cell_27_129_end:
__sbr_cell_27_130:
    shl r11d, cl
__sbr_cell_27_130_end:
__sbr_cell_27_131:
    mov ecx, r10d
__sbr_cell_27_131_end:
__sbr_cell_27_132:
    shr r11d, cl
__sbr_cell_27_132_end:
__sbr_cell_27_133:
    add r11d, eax
__sbr_cell_27_133_end:
__sbr_cell_27_134:
    movsx eax, WORD PTR [r13+r11*4+0]
__sbr_cell_27_134_end:
__sbr_cell_27_135:
    movsx r11d, WORD PTR [r13+r11*4+2]
__sbr_cell_27_135_end:
__sbr_cell_27_136:
    test r11d, r11d
__sbr_cell_27_136_end:
__sbr_cell_27_137:
    js read_sbr_envelope.L59d8
__sbr_cell_27_137_end:
__sbr_cell_27_138:
    mov r10d, r11d
__sbr_cell_27_138_end:
__sbr_cell_27_139:
    jmp read_sbr_envelope.L5a0d
__sbr_cell_27_139_end:
read_sbr_envelope.L59d8:
__sbr_cell_27_140:
    sub r14d, r10d
__sbr_cell_27_140_end:
__sbr_cell_27_141:
    cmp edi, r14d
__sbr_cell_27_141_end:
__sbr_cell_27_142:
    cmovb r14d, edi
__sbr_cell_27_142_end:
__sbr_cell_27_143:
    mov ecx, r14d
__sbr_cell_27_143_end:
__sbr_cell_27_144:
    shr ecx, 3
__sbr_cell_27_144_end:
__sbr_cell_27_145:
    mov r8d, DWORD PTR [r8+rcx*1+0]
__sbr_cell_27_145_end:
__sbr_cell_27_146:
    bswap r8d
__sbr_cell_27_146_end:
__sbr_cell_27_147:
    mov ecx, r14d
__sbr_cell_27_147_end:
__sbr_cell_27_148:
    and cl, 7
__sbr_cell_27_148_end:
__sbr_cell_27_149:
    shl r8d, cl
__sbr_cell_27_149_end:
__sbr_cell_27_150:
    mov ecx, r11d
__sbr_cell_27_150_end:
__sbr_cell_27_151:
    shr r8d, cl
__sbr_cell_27_151_end:
__sbr_cell_27_152:
    add r8d, eax
__sbr_cell_27_152_end:
__sbr_cell_27_153:
    movzx eax, WORD PTR [r13+r8*4+0]
__sbr_cell_27_153_end:
__sbr_cell_27_154:
    movsx r10d, WORD PTR [r13+r8*4+2]
__sbr_cell_27_154_end:
read_sbr_envelope.L5a0d:
__sbr_cell_27_155:
    mov r11d, DWORD PTR [rbp-44]
__sbr_cell_27_155_end:
read_sbr_envelope.L5a11:
__sbr_cell_27_156:
    mov rcx, QWORD PTR [rbp-56]
__sbr_cell_27_156_end:
__sbr_cell_27_157:
    add r14d, r10d
__sbr_cell_27_157_end:
__sbr_cell_27_158:
    cmp edi, r14d
__sbr_cell_27_158_end:
__sbr_cell_27_159:
    cmovb r14d, edi
__sbr_cell_27_159_end:
__sbr_cell_27_160:
    mov DWORD PTR [rdx+8], r14d
__sbr_cell_27_160_end:
__sbr_cell_27_161:
    imul eax, r11d
__sbr_cell_27_161_end:
__sbr_cell_27_162:
    add r9b, al
__sbr_cell_27_162_end:
__sbr_cell_27_163:
    mov rax, QWORD PTR [rbp-88]
__sbr_cell_27_163_end:
__sbr_cell_27_164:
    mov BYTE PTR [rax+rsi*1+0], r9b
__sbr_cell_27_164_end:
__sbr_cell_27_165:
    js read_sbr_envelope.L6044
__sbr_cell_27_165_end:
read_sbr_envelope.L5a38:
__sbr_cell_27_166:
    inc rsi
__sbr_cell_27_166_end:
__sbr_cell_27_167:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_27_167_end:
__sbr_cell_27_168:
    movzx eax, BYTE PTR [rcx+rax*1+12]
__sbr_cell_27_168_end:
__sbr_cell_27_169:
    cmp al, 2
__sbr_cell_27_169_end:
__sbr_cell_27_170:
    jb read_sbr_envelope.L5940
__sbr_cell_27_170_end:
__sbr_cell_27_171:
    jmp read_sbr_envelope.L60bd
__sbr_cell_27_171_end:
__sbr_cell_27_172:
    .nops 1
__sbr_cell_27_172_end:
read_sbr_envelope.L5a60:
__sbr_cell_27_173:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_27_173_end:
__sbr_cell_27_174:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_27_174_end:
__sbr_cell_27_175:
    mov ecx, esi
__sbr_cell_27_175_end:
__sbr_cell_27_176:
    shr ecx, 3
__sbr_cell_27_176_end:
__sbr_cell_27_177:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_27_177_end:
__sbr_cell_27_178:
    bswap eax
__sbr_cell_27_178_end:
__sbr_cell_27_179:
    mov ecx, esi
__sbr_cell_27_179_end:
__sbr_cell_27_180:
    and cl, 7
__sbr_cell_27_180_end:
__sbr_cell_27_181:
    shl eax, cl
__sbr_cell_27_181_end:
__sbr_cell_27_182:
    mov edi, DWORD PTR [rdx+16]
__sbr_cell_27_182_end:
__sbr_cell_27_183:
    movzx ecx, BYTE PTR [rbp-45]
__sbr_cell_27_183_end:
__sbr_cell_27_184:
    shr eax, cl
__sbr_cell_27_184_end:
__sbr_cell_27_185:
    add esi, r10d
__sbr_cell_27_185_end:
__sbr_cell_27_186:
    cmp edi, esi
__sbr_cell_27_186_end:
__sbr_cell_27_187:
    cmovb esi, edi
__sbr_cell_27_187_end:
__sbr_cell_27_188:
    mov DWORD PTR [rdx+8], esi
__sbr_cell_27_188_end:
__sbr_cell_27_189:
    cmp r9, 8
__sbr_cell_27_189_end:
__sbr_cell_27_190:
    je read_sbr_envelope.L60ef
__sbr_cell_27_190_end:
read_sbr_envelope.L5a95:
__sbr_cell_27_191:
    lea rcx, [r9+1]
__sbr_cell_27_191_end:
__sbr_cell_27_192:
    imul eax, r11d
__sbr_cell_27_192_end:
__sbr_cell_27_193:
    mov rbx, rcx
__sbr_cell_27_193_end:
__sbr_cell_27_194:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_27_194_end:
__sbr_cell_27_195:
    shl rcx, 4
__sbr_cell_27_195_end:
__sbr_cell_27_196:
    lea rsi, [r15+86496]
__sbr_cell_27_196_end:
__sbr_cell_27_197:
    mov BYTE PTR [rsi+rcx*1+0], al
__sbr_cell_27_197_end:
__sbr_cell_27_198:
    movzx eax, BYTE PTR [r15+r9*1+13]
__sbr_cell_27_198_end:
__sbr_cell_27_199:
    cmp al, 1
__sbr_cell_27_199_end:
__sbr_cell_27_200:
    ja read_sbr_envelope.L60b8
__sbr_cell_27_200_end:
__sbr_cell_27_201:
    xor r9d, r9d
__sbr_cell_27_201_end:
__sbr_cell_27_202:
    .nops 1
__sbr_cell_27_202_end:
read_sbr_envelope.L5ad0:
__sbr_cell_27_203:
    lea r14, [r9+1]
__sbr_cell_27_203_end:
__sbr_cell_27_204:
    movzx eax, al
__sbr_cell_27_204_end:
__sbr_cell_27_205:
    mov eax, DWORD PTR [r12+rax*4+0]
__sbr_cell_27_205_end:
__sbr_cell_27_206:
    cmp r14, rax
__sbr_cell_27_206_end:
__sbr_cell_27_207:
    jae read_sbr_envelope.L5f90
__sbr_cell_27_207_end:
read_sbr_envelope.L5ae4:
__sbr_cell_27_208:
    mov rax, QWORD PTR [rbp-96]
__sbr_cell_27_208_end:
__sbr_cell_27_209:
    movzx r15d, BYTE PTR [rax+r9*1-1]
__sbr_cell_27_209_end:
__sbr_cell_27_210:
    mov edi, DWORD PTR [rdx+8]
__sbr_cell_27_210_end:
__sbr_cell_27_211:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_27_211_end:
__sbr_cell_27_212:
    mov r12, QWORD PTR [rdx+0]
__sbr_cell_27_212_end:
__sbr_cell_27_213:
    mov eax, edi
__sbr_cell_27_213_end:
__sbr_cell_27_214:
    shr eax, 3
__sbr_cell_27_214_end:
__sbr_cell_27_215:
    mov eax, DWORD PTR [r12+rax*1+0]
__sbr_cell_27_215_end:
__sbr_cell_27_216:
    bswap eax
__sbr_cell_27_216_end:
__sbr_cell_27_217:
    mov ecx, edi
__sbr_cell_27_217_end:
__sbr_cell_27_218:
    and cl, 7
__sbr_cell_27_218_end:
__sbr_cell_27_219:
    shl eax, cl
__sbr_cell_27_219_end:
__sbr_cell_27_220:
    shr eax, 23
__sbr_cell_27_220_end:
__sbr_cell_27_221:
    mov ecx, eax
__sbr_cell_27_221_end:
__sbr_cell_27_222:
    mov rsi, QWORD PTR [rbp-152]
__sbr_cell_27_222_end:
__sbr_cell_27_223:
    movsx eax, WORD PTR [rsi+rcx*4+0]
__sbr_cell_27_223_end:
__sbr_cell_27_224:
    movsx r10d, WORD PTR [rsi+rcx*4+2]
__sbr_cell_27_224_end:
__sbr_cell_27_225:
    test r10d, r10d
__sbr_cell_27_225_end:
__sbr_cell_27_226:
    jns read_sbr_envelope.L5b97
__sbr_cell_27_226_end:
read_sbr_envelope.L5b25:
__sbr_cell_27_227:
    add edi, 9
__sbr_cell_27_227_end:
__sbr_cell_27_228:
    cmp r8d, edi
__sbr_cell_27_228_end:
__sbr_cell_27_229:
    cmovb edi, r8d
__sbr_cell_27_229_end:
__sbr_cell_27_230:
    mov ecx, edi
__sbr_cell_27_230_end:
__sbr_cell_27_231:
    shr ecx, 3
__sbr_cell_27_231_end:
__sbr_cell_27_232:
    mov r11d, DWORD PTR [r12+rcx*1+0]
__sbr_cell_27_232_end:
__sbr_cell_27_233:
    bswap r11d
__sbr_cell_27_233_end:
__sbr_cell_27_234:
    mov ecx, edi
__sbr_cell_27_234_end:
__sbr_cell_27_235:
    and cl, 7
__sbr_cell_27_235_end:
__sbr_cell_27_236:
    shl r11d, cl
__sbr_cell_27_236_end:
__sbr_cell_27_237:
    mov ecx, r10d
__sbr_cell_27_237_end:
__sbr_cell_27_238:
    shr r11d, cl
__sbr_cell_27_238_end:
__sbr_cell_27_239:
    add r11d, eax
__sbr_cell_27_239_end:
__sbr_cell_27_240:
    movsx eax, WORD PTR [rsi+r11*4+0]
__sbr_cell_27_240_end:
__sbr_cell_27_241:
    movsx r11d, WORD PTR [rsi+r11*4+2]
__sbr_cell_27_241_end:
__sbr_cell_27_242:
    test r11d, r11d
__sbr_cell_27_242_end:
__sbr_cell_27_243:
    js read_sbr_envelope.L5b61
__sbr_cell_27_243_end:
__sbr_cell_27_244:
    mov r10d, r11d
__sbr_cell_27_244_end:
__sbr_cell_27_245:
    jmp read_sbr_envelope.L5b93
__sbr_cell_27_245_end:
read_sbr_envelope.L5b61:
__sbr_cell_27_246:
    sub edi, r10d
__sbr_cell_27_246_end:
__sbr_cell_27_247:
    cmp r8d, edi
__sbr_cell_27_247_end:
__sbr_cell_27_248:
    cmovb edi, r8d
__sbr_cell_27_248_end:
__sbr_cell_27_249:
    mov ecx, edi
__sbr_cell_27_249_end:
__sbr_cell_27_250:
    shr ecx, 3
__sbr_cell_27_250_end:
__sbr_cell_27_251:
    mov r10d, DWORD PTR [r12+rcx*1+0]
__sbr_cell_27_251_end:
__sbr_cell_27_252:
    bswap r10d
__sbr_cell_27_252_end:
__sbr_cell_27_253:
    mov ecx, edi
__sbr_cell_27_253_end:
__sbr_cell_27_254:
    and cl, 7
__sbr_cell_27_254_end:
__sbr_cell_27_255:
    shl r10d, cl
__sbr_cell_27_255_end:
__sbr_cell_27_256:
    mov ecx, r11d
__sbr_cell_27_256_end:
__sbr_cell_27_257:
    shr r10d, cl
__sbr_cell_27_257_end:
__sbr_cell_27_258:
    add r10d, eax
__sbr_cell_27_258_end:
__sbr_cell_27_259:
    movzx eax, WORD PTR [rsi+r10*4+0]
__sbr_cell_27_259_end:
__sbr_cell_27_260:
    movsx r10d, WORD PTR [rsi+r10*4+2]
__sbr_cell_27_260_end:
read_sbr_envelope.L5b93:
__sbr_cell_27_261:
    mov r11d, DWORD PTR [rbp-44]
__sbr_cell_27_261_end:
read_sbr_envelope.L5b97:
__sbr_cell_27_262:
    mov r12, QWORD PTR [rbp-64]
__sbr_cell_27_262_end:
__sbr_cell_27_263:
    add edi, r10d
__sbr_cell_27_263_end:
__sbr_cell_27_264:
    cmp r8d, edi
__sbr_cell_27_264_end:
__sbr_cell_27_265:
    cmovb edi, r8d
__sbr_cell_27_265_end:
__sbr_cell_27_266:
    mov DWORD PTR [rdx+8], edi
__sbr_cell_27_266_end:
__sbr_cell_27_267:
    cmp r9, 47
__sbr_cell_27_267_end:
__sbr_cell_27_268:
    je read_sbr_envelope.L60c7
__sbr_cell_27_268_end:
__sbr_cell_27_269:
    imul eax, r11d
__sbr_cell_27_269_end:
__sbr_cell_27_270:
    add r15b, al
__sbr_cell_27_270_end:
__sbr_cell_27_271:
    mov rax, QWORD PTR [rbp-96]
__sbr_cell_27_271_end:
__sbr_cell_27_272:
    mov BYTE PTR [rax+r9*1+0], r15b
__sbr_cell_27_272_end:
__sbr_cell_27_273:
    js read_sbr_envelope.L603e
__sbr_cell_27_273_end:
read_sbr_envelope.L5bc7:
__sbr_cell_27_274:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_27_274_end:
__sbr_cell_27_275:
    movzx eax, BYTE PTR [rax+rbx*1+12]
__sbr_cell_27_275_end:
__sbr_cell_27_276:
    mov r9, r14
__sbr_cell_27_276_end:
__sbr_cell_27_277:
    cmp al, 2
__sbr_cell_27_277_end:
__sbr_cell_27_278:
    jb read_sbr_envelope.L5ad0
__sbr_cell_27_278_end:
__sbr_cell_27_279:
    jmp read_sbr_envelope.L60b8
__sbr_cell_27_279_end:
read_sbr_envelope.L5be0:
__sbr_cell_27_280:
    movzx eax, al
__sbr_cell_27_280_end:
__sbr_cell_27_281:
    test eax, eax
__sbr_cell_27_281_end:
__sbr_cell_27_282:
    jne read_sbr_envelope.L5ca5
__sbr_cell_27_282_end:
__sbr_cell_27_283:
    cmp DWORD PTR [r12+0], 0
__sbr_cell_27_283_end:
__sbr_cell_27_284:
    je read_sbr_envelope.L5f90
__sbr_cell_27_284_end:
read_sbr_envelope.L5bf6:
__sbr_cell_27_285:
    mov rax, QWORD PTR [rbp-104]
__sbr_cell_27_285_end:
__sbr_cell_27_286:
    lea rdi, [rax+rax*2+0]
__sbr_cell_27_286_end:
__sbr_cell_27_287:
    shl rdi, 4
__sbr_cell_27_287_end:
__sbr_cell_27_288:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_27_288_end:
__sbr_cell_27_289:
    add rax, 86496
__sbr_cell_27_289_end:
__sbr_cell_27_290:
    add rdi, rax
__sbr_cell_27_290_end:
__sbr_cell_27_291:
    mov rcx, QWORD PTR [rbp-72]
__sbr_cell_27_291_end:
__sbr_cell_27_292:
    lea rsi, [rcx+rcx*2+0]
__sbr_cell_27_292_end:
__sbr_cell_27_293:
    shl rsi, 4
__sbr_cell_27_293_end:
__sbr_cell_27_294:
    add rsi, rax
__sbr_cell_27_294_end:
__sbr_cell_27_295:
    mov QWORD PTR [rbp-128], rdi
__sbr_cell_27_295_end:
__sbr_cell_27_296:
    movzx r15d, BYTE PTR [rdi+0]
__sbr_cell_27_296_end:
read_sbr_envelope.L5c26:
__sbr_cell_27_297:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_27_297_end:
__sbr_cell_27_298:
    mov edi, DWORD PTR [rdx+16]
__sbr_cell_27_298_end:
__sbr_cell_27_299:
    mov r8, QWORD PTR [rdx+0]
__sbr_cell_27_299_end:
__sbr_cell_27_300:
    mov eax, r9d
__sbr_cell_27_300_end:
__sbr_cell_27_301:
    shr eax, 3
__sbr_cell_27_301_end:
__sbr_cell_27_302:
    mov eax, DWORD PTR [r8+rax*1+0]
__sbr_cell_27_302_end:
__sbr_cell_27_303:
    bswap eax
__sbr_cell_27_303_end:
__sbr_cell_27_304:
    mov ecx, r9d
__sbr_cell_27_304_end:
__sbr_cell_27_305:
    and cl, 7
__sbr_cell_27_305_end:
__sbr_cell_27_306:
    shl eax, cl
__sbr_cell_27_306_end:
__sbr_cell_27_307:
    shr eax, 23
__sbr_cell_27_307_end:
__sbr_cell_27_308:
    mov ecx, eax
__sbr_cell_27_308_end:
__sbr_cell_27_309:
    movsx eax, WORD PTR [r13+rcx*4+0]
__sbr_cell_27_309_end:
__sbr_cell_27_310:
    movsx r10d, WORD PTR [r13+rcx*4+2]
__sbr_cell_27_310_end:
__sbr_cell_27_311:
    test r10d, r10d
__sbr_cell_27_311_end:
__sbr_cell_27_312:
    jns read_sbr_envelope.L5e2d
__sbr_cell_27_312_end:
read_sbr_envelope.L5c5e:
__sbr_cell_27_313:
    add r9d, 9
__sbr_cell_27_313_end:
__sbr_cell_27_314:
    cmp edi, r9d
__sbr_cell_27_314_end:
__sbr_cell_27_315:
    cmovb r9d, edi
__sbr_cell_27_315_end:
__sbr_cell_27_316:
    mov ecx, r9d
__sbr_cell_27_316_end:
__sbr_cell_27_317:
    shr ecx, 3
__sbr_cell_27_317_end:
__sbr_cell_27_318:
    mov r11d, DWORD PTR [r8+rcx*1+0]
__sbr_cell_27_318_end:
__sbr_cell_27_319:
    bswap r11d
__sbr_cell_27_319_end:
__sbr_cell_27_320:
    mov ecx, r9d
__sbr_cell_27_320_end:
__sbr_cell_27_321:
    and cl, 7
__sbr_cell_27_321_end:
__sbr_cell_27_322:
    shl r11d, cl
__sbr_cell_27_322_end:
__sbr_cell_27_323:
    mov ecx, r10d
__sbr_cell_27_323_end:
__sbr_cell_27_324:
    shr r11d, cl
__sbr_cell_27_324_end:
__sbr_cell_27_325:
    add r11d, eax
__sbr_cell_27_325_end:
__sbr_cell_27_326:
    movsx eax, WORD PTR [r13+r11*4+0]
__sbr_cell_27_326_end:
__sbr_cell_27_327:
    movsx r11d, WORD PTR [r13+r11*4+2]
__sbr_cell_27_327_end:
__sbr_cell_27_328:
    test r11d, r11d
__sbr_cell_27_328_end:
__sbr_cell_27_329:
    js read_sbr_envelope.L5df4
__sbr_cell_27_329_end:
__sbr_cell_27_330:
    mov r10d, r11d
__sbr_cell_27_330_end:
__sbr_cell_27_331:
    jmp read_sbr_envelope.L5e29
__sbr_cell_27_331_end:
read_sbr_envelope.L5ca5:
__sbr_cell_27_332:
    cmp eax, 1
__sbr_cell_27_332_end:
__sbr_cell_27_333:
    jne read_sbr_envelope.L60c2
__sbr_cell_27_333_end:
__sbr_cell_27_334:
    mov rax, QWORD PTR [rbp-104]
__sbr_cell_27_334_end:
__sbr_cell_27_335:
    lea r15, [rax+rax*2+0]
__sbr_cell_27_335_end:
__sbr_cell_27_336:
    shl r15, 4
__sbr_cell_27_336_end:
__sbr_cell_27_337:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_27_337_end:
__sbr_cell_27_338:
    add rax, 86496
__sbr_cell_27_338_end:
__sbr_cell_27_339:
    add r15, rax
__sbr_cell_27_339_end:
__sbr_cell_27_340:
    mov al, 1
__sbr_cell_27_340_end:
__sbr_cell_27_341:
    xor esi, esi
__sbr_cell_27_341_end:
__sbr_cell_27_342:
    .nops 1
__sbr_cell_27_342_end:
read_sbr_envelope.L5cd0:
__sbr_cell_27_343:
    movzx eax, al
__sbr_cell_27_343_end:
__sbr_cell_27_344:
    mov eax, DWORD PTR [r12+rax*4+0]
__sbr_cell_27_344_end:
__sbr_cell_27_345:
    cmp rsi, rax
__sbr_cell_27_345_end:
__sbr_cell_27_346:
    jae read_sbr_envelope.L5f90
__sbr_cell_27_346_end:
__sbr_cell_27_347:
    cmp QWORD PTR [rbp-144], rsi
__sbr_cell_27_347_end:
__sbr_cell_27_348:
    je read_sbr_envelope.L60d6
__sbr_cell_27_348_end:
read_sbr_envelope.L5ced:
__sbr_cell_27_349:
    mov rax, QWORD PTR [rbp-136]
__sbr_cell_27_349_end:
__sbr_cell_27_350:
    add eax, esi
__sbr_cell_27_350_end:
__sbr_cell_27_351:
    shr eax, 1
__sbr_cell_27_351_end:
__sbr_cell_27_352:
    movzx r9d, BYTE PTR [r15+rax*1+0]
__sbr_cell_27_352_end:
read_sbr_envelope.L5cfd:
__sbr_cell_27_353:
    mov r14d, DWORD PTR [rdx+8]
__sbr_cell_27_353_end:
__sbr_cell_27_354:
    mov edi, DWORD PTR [rdx+16]
__sbr_cell_27_354_end:
__sbr_cell_27_355:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_27_355_end:
__sbr_cell_27_356:
    mov ecx, r14d
__sbr_cell_27_356_end:
__sbr_cell_27_357:
    shr ecx, 3
__sbr_cell_27_357_end:
__sbr_cell_27_358:
    mov r8d, DWORD PTR [rax+rcx*1+0]
__sbr_cell_27_358_end:
__sbr_cell_27_359:
    bswap r8d
__sbr_cell_27_359_end:
__sbr_cell_27_360:
    mov ecx, r14d
__sbr_cell_27_360_end:
__sbr_cell_27_361:
    and cl, 7
__sbr_cell_27_361_end:
__sbr_cell_27_362:
    shl r8d, cl
__sbr_cell_27_362_end:
__sbr_cell_27_363:
    shr r8d, 23
__sbr_cell_27_363_end:
__sbr_cell_27_364:
    mov ecx, r8d
__sbr_cell_27_364_end:
__sbr_cell_27_365:
    movsx r8d, WORD PTR [r13+rcx*4+0]
__sbr_cell_27_365_end:
__sbr_cell_27_366:
    movsx r10d, WORD PTR [r13+rcx*4+2]
__sbr_cell_27_366_end:
__sbr_cell_27_367:
    test r10d, r10d
__sbr_cell_27_367_end:
__sbr_cell_27_368:
    jns read_sbr_envelope.L5daa
__sbr_cell_27_368_end:
read_sbr_envelope.L5d35:
__sbr_cell_27_369:
    add r14d, 9
__sbr_cell_27_369_end:
__sbr_cell_27_370:
    cmp edi, r14d
__sbr_cell_27_370_end:
__sbr_cell_27_371:
    cmovb r14d, edi
__sbr_cell_27_371_end:
__sbr_cell_27_372:
    mov ecx, r14d
__sbr_cell_27_372_end:
__sbr_cell_27_373:
    shr ecx, 3
__sbr_cell_27_373_end:
__sbr_cell_27_374:
    mov r11d, DWORD PTR [rax+rcx*1+0]
__sbr_cell_27_374_end:
__sbr_cell_27_375:
    bswap r11d
__sbr_cell_27_375_end:
__sbr_cell_27_376:
    mov ecx, r14d
__sbr_cell_27_376_end:
__sbr_cell_27_377:
    and cl, 7
__sbr_cell_27_377_end:
__sbr_cell_27_378:
    shl r11d, cl
__sbr_cell_27_378_end:
__sbr_cell_27_379:
    mov ecx, r10d
__sbr_cell_27_379_end:
__sbr_cell_27_380:
    shr r11d, cl
__sbr_cell_27_380_end:
__sbr_cell_27_381:
    add r11d, r8d
__sbr_cell_27_381_end:
__sbr_cell_27_382:
    movsx r8d, WORD PTR [r13+r11*4+0]
__sbr_cell_27_382_end:
__sbr_cell_27_383:
    movsx r11d, WORD PTR [r13+r11*4+2]
__sbr_cell_27_383_end:
__sbr_cell_27_384:
    test r11d, r11d
__sbr_cell_27_384_end:
__sbr_cell_27_385:
    js read_sbr_envelope.L5d75
__sbr_cell_27_385_end:
__sbr_cell_27_386:
    mov r10d, r11d
__sbr_cell_27_386_end:
__sbr_cell_27_387:
    jmp read_sbr_envelope.L5da6
__sbr_cell_27_387_end:
read_sbr_envelope.L5d75:
__sbr_cell_27_388:
    sub r14d, r10d
__sbr_cell_27_388_end:
__sbr_cell_27_389:
    cmp edi, r14d
__sbr_cell_27_389_end:
__sbr_cell_27_390:
    cmovb r14d, edi
__sbr_cell_27_390_end:
__sbr_cell_27_391:
    mov ecx, r14d
__sbr_cell_27_391_end:
__sbr_cell_27_392:
    shr ecx, 3
__sbr_cell_27_392_end:
__sbr_cell_27_393:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_27_393_end:
__sbr_cell_27_394:
    bswap eax
__sbr_cell_27_394_end:
__sbr_cell_27_395:
    mov ecx, r14d
__sbr_cell_27_395_end:
__sbr_cell_27_396:
    and cl, 7
__sbr_cell_27_396_end:
__sbr_cell_27_397:
    shl eax, cl
__sbr_cell_27_397_end:
__sbr_cell_27_398:
    mov ecx, r11d
__sbr_cell_27_398_end:
__sbr_cell_27_399:
    shr eax, cl
__sbr_cell_27_399_end:
__sbr_cell_27_400:
    add eax, r8d
__sbr_cell_27_400_end:
__sbr_cell_27_401:
    movzx r8d, WORD PTR [r13+rax*4+0]
__sbr_cell_27_401_end:
__sbr_cell_27_402:
    movsx r10d, WORD PTR [r13+rax*4+2]
__sbr_cell_27_402_end:
read_sbr_envelope.L5da6:
__sbr_cell_27_403:
    mov r11d, DWORD PTR [rbp-44]
__sbr_cell_27_403_end:
read_sbr_envelope.L5daa:
__sbr_cell_27_404:
    add r14d, r10d
__sbr_cell_27_404_end:
__sbr_cell_27_405:
    cmp edi, r14d
__sbr_cell_27_405_end:
__sbr_cell_27_406:
    cmovb r14d, edi
__sbr_cell_27_406_end:
__sbr_cell_27_407:
    mov DWORD PTR [rdx+8], r14d
__sbr_cell_27_407_end:
__sbr_cell_27_408:
    cmp rsi, 48
__sbr_cell_27_408_end:
__sbr_cell_27_409:
    je read_sbr_envelope.L60d1
__sbr_cell_27_409_end:
__sbr_cell_27_410:
    imul r8d, r11d
__sbr_cell_27_410_end:
__sbr_cell_27_411:
    add r9b, r8b
__sbr_cell_27_411_end:
__sbr_cell_27_412:
    mov rax, QWORD PTR [rbp-88]
__sbr_cell_27_412_end:
__sbr_cell_27_413:
    mov BYTE PTR [rax+rsi*1+0], r9b
__sbr_cell_27_413_end:
__sbr_cell_27_414:
    js read_sbr_envelope.L6044
__sbr_cell_27_414_end:
read_sbr_envelope.L5dd7:
__sbr_cell_27_415:
    inc rsi
__sbr_cell_27_415_end:
__sbr_cell_27_416:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_27_416_end:
__sbr_cell_27_417:
    mov rcx, QWORD PTR [rbp-56]
__sbr_cell_27_417_end:
__sbr_cell_27_418:
    movzx eax, BYTE PTR [rcx+rax*1+12]
__sbr_cell_27_418_end:
__sbr_cell_27_419:
    cmp al, 2
__sbr_cell_27_419_end:
__sbr_cell_27_420:
    jb read_sbr_envelope.L5cd0
__sbr_cell_27_420_end:
__sbr_cell_27_421:
    jmp read_sbr_envelope.L60c2
__sbr_cell_27_421_end:
read_sbr_envelope.L5df4:
__sbr_cell_27_422:
    sub r9d, r10d
__sbr_cell_27_422_end:
__sbr_cell_27_423:
    cmp edi, r9d
__sbr_cell_27_423_end:
__sbr_cell_27_424:
    cmovb r9d, edi
__sbr_cell_27_424_end:
__sbr_cell_27_425:
    mov ecx, r9d
__sbr_cell_27_425_end:
__sbr_cell_27_426:
    shr ecx, 3
__sbr_cell_27_426_end:
__sbr_cell_27_427:
    mov r8d, DWORD PTR [r8+rcx*1+0]
__sbr_cell_27_427_end:
__sbr_cell_27_428:
    bswap r8d
__sbr_cell_27_428_end:
__sbr_cell_27_429:
    mov ecx, r9d
__sbr_cell_27_429_end:
__sbr_cell_27_430:
    and cl, 7
__sbr_cell_27_430_end:
__sbr_cell_27_431:
    shl r8d, cl
__sbr_cell_27_431_end:
__sbr_cell_27_432:
    mov ecx, r11d
__sbr_cell_27_432_end:
__sbr_cell_27_433:
    shr r8d, cl
__sbr_cell_27_433_end:
__sbr_cell_27_434:
    add r8d, eax
__sbr_cell_27_434_end:
__sbr_cell_27_435:
    movzx eax, WORD PTR [r13+r8*4+0]
__sbr_cell_27_435_end:
__sbr_cell_27_436:
    movsx r10d, WORD PTR [r13+r8*4+2]
__sbr_cell_27_436_end:
read_sbr_envelope.L5e29:
__sbr_cell_27_437:
    mov r11d, DWORD PTR [rbp-44]
__sbr_cell_27_437_end:
read_sbr_envelope.L5e2d:
__sbr_cell_27_438:
    add r9d, r10d
__sbr_cell_27_438_end:
__sbr_cell_27_439:
    cmp edi, r9d
__sbr_cell_27_439_end:
__sbr_cell_27_440:
    cmovb r9d, edi
__sbr_cell_27_440_end:
__sbr_cell_27_441:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_27_441_end:
__sbr_cell_27_442:
    imul eax, r11d
__sbr_cell_27_442_end:
__sbr_cell_27_443:
    add r15b, al
__sbr_cell_27_443_end:
__sbr_cell_27_444:
    mov BYTE PTR [rsi+0], r15b
__sbr_cell_27_444_end:
__sbr_cell_27_445:
    js read_sbr_envelope.L603e
__sbr_cell_27_445_end:
read_sbr_envelope.L5e4b:
__sbr_cell_27_446:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_27_446_end:
__sbr_cell_27_447:
    mov rcx, QWORD PTR [rbp-56]
__sbr_cell_27_447_end:
__sbr_cell_27_448:
    movzx eax, BYTE PTR [rcx+rax*1+12]
__sbr_cell_27_448_end:
__sbr_cell_27_449:
    cmp al, 1
__sbr_cell_27_449_end:
__sbr_cell_27_450:
    ja read_sbr_envelope.L60db
__sbr_cell_27_450_end:
__sbr_cell_27_451:
    xor r9d, r9d
__sbr_cell_27_451_end:
__sbr_cell_27_452:
    mov esi, DWORD PTR [rbp-108]
__sbr_cell_27_452_end:
__sbr_cell_27_453:
    .nops 1
__sbr_cell_27_453_end:
read_sbr_envelope.L5e70:
__sbr_cell_27_454:
    lea r14, [r9+1]
__sbr_cell_27_454_end:
__sbr_cell_27_455:
    movzx eax, al
__sbr_cell_27_455_end:
__sbr_cell_27_456:
    mov eax, DWORD PTR [r12+rax*4+0]
__sbr_cell_27_456_end:
__sbr_cell_27_457:
    cmp r14, rax
__sbr_cell_27_457_end:
__sbr_cell_27_458:
    jae read_sbr_envelope.L5f90
__sbr_cell_27_458_end:
__sbr_cell_27_459:
    cmp esi, 48
__sbr_cell_27_459_end:
__sbr_cell_27_460:
    jae read_sbr_envelope.L60e0
__sbr_cell_27_460_end:
read_sbr_envelope.L5e8d:
__sbr_cell_27_461:
    mov eax, esi
__sbr_cell_27_461_end:
__sbr_cell_27_462:
    mov rcx, QWORD PTR [rbp-128]
__sbr_cell_27_462_end:
__sbr_cell_27_463:
    movzx r15d, BYTE PTR [rcx+rax*1+0]
__sbr_cell_27_463_end:
__sbr_cell_27_464:
    mov edi, DWORD PTR [rdx+8]
__sbr_cell_27_464_end:
__sbr_cell_27_465:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_27_465_end:
__sbr_cell_27_466:
    mov r12, QWORD PTR [rdx+0]
__sbr_cell_27_466_end:
__sbr_cell_27_467:
    mov eax, edi
__sbr_cell_27_467_end:
__sbr_cell_27_468:
    shr eax, 3
__sbr_cell_27_468_end:
__sbr_cell_27_469:
    mov eax, DWORD PTR [r12+rax*1+0]
__sbr_cell_27_469_end:
__sbr_cell_27_470:
    bswap eax
__sbr_cell_27_470_end:
__sbr_cell_27_471:
    mov ecx, edi
__sbr_cell_27_471_end:
__sbr_cell_27_472:
    and cl, 7
__sbr_cell_27_472_end:
__sbr_cell_27_473:
    shl eax, cl
__sbr_cell_27_473_end:
__sbr_cell_27_474:
    shr eax, 23
__sbr_cell_27_474_end:
__sbr_cell_27_475:
    mov ecx, eax
__sbr_cell_27_475_end:
__sbr_cell_27_476:
    movsx eax, WORD PTR [r13+rcx*4+0]
__sbr_cell_27_476_end:
__sbr_cell_27_477:
    movsx r10d, WORD PTR [r13+rcx*4+2]
__sbr_cell_27_477_end:
__sbr_cell_27_478:
    test r10d, r10d
__sbr_cell_27_478_end:
__sbr_cell_27_479:
    jns read_sbr_envelope.L5f3e
__sbr_cell_27_479_end:
read_sbr_envelope.L5eca:
__sbr_cell_27_480:
    add edi, 9
__sbr_cell_27_480_end:
__sbr_cell_27_481:
    cmp r8d, edi
__sbr_cell_27_481_end:
__sbr_cell_27_482:
    cmovb edi, r8d
__sbr_cell_27_482_end:
__sbr_cell_27_483:
    mov ecx, edi
__sbr_cell_27_483_end:
__sbr_cell_27_484:
    shr ecx, 3
__sbr_cell_27_484_end:
__sbr_cell_27_485:
    mov r11d, DWORD PTR [r12+rcx*1+0]
__sbr_cell_27_485_end:
__sbr_cell_27_486:
    bswap r11d
__sbr_cell_27_486_end:
__sbr_cell_27_487:
    mov ecx, edi
__sbr_cell_27_487_end:
__sbr_cell_27_488:
    and cl, 7
__sbr_cell_27_488_end:
__sbr_cell_27_489:
    shl r11d, cl
__sbr_cell_27_489_end:
__sbr_cell_27_490:
    mov ecx, r10d
__sbr_cell_27_490_end:
__sbr_cell_27_491:
    shr r11d, cl
__sbr_cell_27_491_end:
__sbr_cell_27_492:
    add r11d, eax
__sbr_cell_27_492_end:
__sbr_cell_27_493:
    movsx eax, WORD PTR [r13+r11*4+0]
__sbr_cell_27_493_end:
__sbr_cell_27_494:
    movsx r11d, WORD PTR [r13+r11*4+2]
__sbr_cell_27_494_end:
__sbr_cell_27_495:
    test r11d, r11d
__sbr_cell_27_495_end:
__sbr_cell_27_496:
    js read_sbr_envelope.L5f07
__sbr_cell_27_496_end:
__sbr_cell_27_497:
    mov r10d, r11d
__sbr_cell_27_497_end:
__sbr_cell_27_498:
    jmp read_sbr_envelope.L5f3a
__sbr_cell_27_498_end:
read_sbr_envelope.L5f07:
__sbr_cell_27_499:
    sub edi, r10d
__sbr_cell_27_499_end:
__sbr_cell_27_500:
    cmp r8d, edi
__sbr_cell_27_500_end:
__sbr_cell_27_501:
    cmovb edi, r8d
__sbr_cell_27_501_end:
__sbr_cell_27_502:
    mov ecx, edi
__sbr_cell_27_502_end:
__sbr_cell_27_503:
    shr ecx, 3
__sbr_cell_27_503_end:
__sbr_cell_27_504:
    mov r10d, DWORD PTR [r12+rcx*1+0]
__sbr_cell_27_504_end:
__sbr_cell_27_505:
    bswap r10d
__sbr_cell_27_505_end:
__sbr_cell_27_506:
    mov ecx, edi
__sbr_cell_27_506_end:
__sbr_cell_27_507:
    and cl, 7
__sbr_cell_27_507_end:
__sbr_cell_27_508:
    shl r10d, cl
__sbr_cell_27_508_end:
__sbr_cell_27_509:
    mov ecx, r11d
__sbr_cell_27_509_end:
__sbr_cell_27_510:
    shr r10d, cl
__sbr_cell_27_510_end:
__sbr_cell_27_511:
    add r10d, eax
__sbr_cell_27_511_end:
__sbr_cell_27_512:
    movzx eax, WORD PTR [r13+r10*4+0]
__sbr_cell_27_512_end:
__sbr_cell_27_513:
    movsx r10d, WORD PTR [r13+r10*4+2]
__sbr_cell_27_513_end:
read_sbr_envelope.L5f3a:
__sbr_cell_27_514:
    mov r11d, DWORD PTR [rbp-44]
__sbr_cell_27_514_end:
read_sbr_envelope.L5f3e:
__sbr_cell_27_515:
    mov r12, QWORD PTR [rbp-64]
__sbr_cell_27_515_end:
__sbr_cell_27_516:
    add edi, r10d
__sbr_cell_27_516_end:
__sbr_cell_27_517:
    cmp r8d, edi
__sbr_cell_27_517_end:
__sbr_cell_27_518:
    cmovb edi, r8d
__sbr_cell_27_518_end:
__sbr_cell_27_519:
    mov DWORD PTR [rdx+8], edi
__sbr_cell_27_519_end:
__sbr_cell_27_520:
    cmp r9, 47
__sbr_cell_27_520_end:
__sbr_cell_27_521:
    je read_sbr_envelope.L60e5
__sbr_cell_27_521_end:
__sbr_cell_27_522:
    imul eax, r11d
__sbr_cell_27_522_end:
__sbr_cell_27_523:
    add r15b, al
__sbr_cell_27_523_end:
__sbr_cell_27_524:
    mov rax, QWORD PTR [rbp-96]
__sbr_cell_27_524_end:
__sbr_cell_27_525:
    mov BYTE PTR [rax+r9*1+0], r15b
__sbr_cell_27_525_end:
__sbr_cell_27_526:
    js read_sbr_envelope.L603e
__sbr_cell_27_526_end:
read_sbr_envelope.L5f6e:
__sbr_cell_27_527:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_27_527_end:
__sbr_cell_27_528:
    mov rcx, QWORD PTR [rbp-56]
__sbr_cell_27_528_end:
__sbr_cell_27_529:
    movzx eax, BYTE PTR [rcx+rax*1+12]
__sbr_cell_27_529_end:
__sbr_cell_27_530:
    add esi, 2
__sbr_cell_27_530_end:
__sbr_cell_27_531:
    mov r9, r14
__sbr_cell_27_531_end:
__sbr_cell_27_532:
    cmp al, 2
__sbr_cell_27_532_end:
__sbr_cell_27_533:
    jb read_sbr_envelope.L5e70
__sbr_cell_27_533_end:
__sbr_cell_27_534:
    jmp read_sbr_envelope.L60db
__sbr_cell_27_534_end:
__sbr_cell_27_535:
    .nops 1
__sbr_cell_27_535_end:
read_sbr_envelope.L5f90:
__sbr_cell_27_536:
    mov rax, QWORD PTR [rbp-120]
__sbr_cell_27_536_end:
__sbr_cell_27_537:
    cmp DWORD PTR [rax+16], 0
__sbr_cell_27_537_end:
__sbr_cell_27_538:
    mov r10d, DWORD PTR [rbp-112]
__sbr_cell_27_538_end:
__sbr_cell_27_539:
    mov r9, QWORD PTR [rbp-104]
__sbr_cell_27_539_end:
__sbr_cell_27_540:
    mov r15, QWORD PTR [rbp-56]
__sbr_cell_27_540_end:
__sbr_cell_27_541:
    je read_sbr_envelope.L6019
__sbr_cell_27_541_end:
__sbr_cell_27_542:
    cmp DWORD PTR [rax+20], 0
__sbr_cell_27_542_end:
__sbr_cell_27_543:
    je read_sbr_envelope.L6019
__sbr_cell_27_543_end:
read_sbr_envelope.L5fac:
__sbr_cell_27_544:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_27_544_end:
__sbr_cell_27_545:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_27_545_end:
__sbr_cell_27_546:
    mov ecx, esi
__sbr_cell_27_546_end:
__sbr_cell_27_547:
    shr ecx, 3
__sbr_cell_27_547_end:
__sbr_cell_27_548:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_27_548_end:
__sbr_cell_27_549:
    bswap eax
__sbr_cell_27_549_end:
__sbr_cell_27_550:
    mov ecx, esi
__sbr_cell_27_550_end:
__sbr_cell_27_551:
    and cl, 7
__sbr_cell_27_551_end:
__sbr_cell_27_552:
    shl eax, cl
__sbr_cell_27_552_end:
__sbr_cell_27_553:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_27_553_end:
__sbr_cell_27_554:
    shr eax, 31
__sbr_cell_27_554_end:
__sbr_cell_27_555:
    inc esi
__sbr_cell_27_555_end:
__sbr_cell_27_556:
    cmp ecx, esi
__sbr_cell_27_556_end:
__sbr_cell_27_557:
    cmovb esi, ecx
__sbr_cell_27_557_end:
__sbr_cell_27_558:
    mov DWORD PTR [rdx+8], esi
__sbr_cell_27_558_end:
__sbr_cell_27_559:
    cmp r9, 6
__sbr_cell_27_559_end:
__sbr_cell_27_560:
    jae read_sbr_envelope.L60f9
__sbr_cell_27_560_end:
read_sbr_envelope.L5fdd:
__sbr_cell_27_561:
    mov BYTE PTR [r15+r9*1+88756], al
__sbr_cell_27_561_end:
__sbr_cell_27_562:
    test al, al
__sbr_cell_27_562_end:
__sbr_cell_27_563:
    je read_sbr_envelope.L6019
__sbr_cell_27_563_end:
read_sbr_envelope.L5fe9:
__sbr_cell_27_564:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_27_564_end:
__sbr_cell_27_565:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_27_565_end:
__sbr_cell_27_566:
    mov esi, eax
__sbr_cell_27_566_end:
__sbr_cell_27_567:
    shr esi, 3
__sbr_cell_27_567_end:
__sbr_cell_27_568:
    mov esi, DWORD PTR [rcx+rsi*1+0]
__sbr_cell_27_568_end:
__sbr_cell_27_569:
    bswap esi
__sbr_cell_27_569_end:
__sbr_cell_27_570:
    mov ecx, eax
__sbr_cell_27_570_end:
__sbr_cell_27_571:
    and cl, 7
__sbr_cell_27_571_end:
__sbr_cell_27_572:
    shl esi, cl
__sbr_cell_27_572_end:
__sbr_cell_27_573:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_27_573_end:
__sbr_cell_27_574:
    shr esi, 30
__sbr_cell_27_574_end:
__sbr_cell_27_575:
    add eax, 2
__sbr_cell_27_575_end:
__sbr_cell_27_576:
    cmp ecx, eax
__sbr_cell_27_576_end:
__sbr_cell_27_577:
    cmovb eax, ecx
__sbr_cell_27_577_end:
__sbr_cell_27_578:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_27_578_end:
__sbr_cell_27_579:
    mov BYTE PTR [r15+r9*1+88762], sil
__sbr_cell_27_579_end:
read_sbr_envelope.L6019:
__sbr_cell_27_580:
    inc r9
__sbr_cell_27_580_end:
__sbr_cell_27_581:
    mov r8d, DWORD PTR [r15+8]
__sbr_cell_27_581_end:
__sbr_cell_27_582:
    cmp r9, r8
__sbr_cell_27_582_end:
__sbr_cell_27_583:
    jae read_sbr_envelope.L606a
__sbr_cell_27_583_end:
__sbr_cell_27_584:
    add QWORD PTR [rbp-88], 48
__sbr_cell_27_584_end:
__sbr_cell_27_585:
    add QWORD PTR [rbp-96], 48
__sbr_cell_27_585_end:
__sbr_cell_27_586:
    cmp r9, 9
__sbr_cell_27_586_end:
__sbr_cell_27_587:
    jne read_sbr_envelope.L58fd
__sbr_cell_27_587_end:
__sbr_cell_27_588:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_588_end:
read_sbr_envelope.L603e:
__sbr_cell_27_589:
    movzx ecx, r15b
__sbr_cell_27_589_end:
__sbr_cell_27_590:
    jmp read_sbr_envelope.L6048
__sbr_cell_27_590_end:
read_sbr_envelope.L6044:
__sbr_cell_27_591:
    movzx ecx, r9b
__sbr_cell_27_591_end:
read_sbr_envelope.L6048:
__sbr_cell_27_592:
    mov rax, QWORD PTR [rbp-80]
__sbr_cell_27_592_end:
__sbr_cell_27_593:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_27_593_end:
__sbr_cell_27_594:
    lea rdx, [rip+L_str_30]
__sbr_cell_27_594_end:
__sbr_cell_27_595:
    mov esi, 16
__sbr_cell_27_595_end:
__sbr_cell_27_596:
    xor eax, eax
__sbr_cell_27_596_end:
__sbr_cell_27_597:
    call av_log
__sbr_cell_27_597_end:
read_sbr_envelope.L6063:
__sbr_cell_27_598:
    mov eax, 3199971767
__sbr_cell_27_598_end:
__sbr_cell_27_599:
    jmp read_sbr_envelope.L60a6
__sbr_cell_27_599_end:
read_sbr_envelope.L606a:
__sbr_cell_27_600:
    cmp r8d, 10
__sbr_cell_27_600_end:
__sbr_cell_27_601:
    mov eax, 0
__sbr_cell_27_601_end:
__sbr_cell_27_602:
    jae read_sbr_envelope.L60f4
__sbr_cell_27_602_end:
read_sbr_envelope.L6075:
__sbr_cell_27_603:
    mov ecx, r8d
__sbr_cell_27_603_end:
__sbr_cell_27_604:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_27_604_end:
__sbr_cell_27_605:
    shl rcx, 4
__sbr_cell_27_605_end:
__sbr_cell_27_606:
    vmovups ymm0, YMMWORD PTR [r15+rcx*1+86496]
__sbr_cell_27_606_end:
__sbr_cell_27_607:
    vmovups ymm1, YMMWORD PTR [r15+rcx*1+86512]
__sbr_cell_27_607_end:
__sbr_cell_27_608:
    vmovups YMMWORD PTR [r15+86512], ymm1
__sbr_cell_27_608_end:
__sbr_cell_27_609:
    vmovaps YMMWORD PTR [r15+86496], ymm0
__sbr_cell_27_609_end:
read_sbr_envelope.L60a6:
__sbr_cell_27_610:
    add rsp, 120
__sbr_cell_27_610_end:
__sbr_cell_27_611:
    pop rbx
__sbr_cell_27_611_end:
__sbr_cell_27_612:
    pop r12
__sbr_cell_27_612_end:
__sbr_cell_27_613:
    pop r13
__sbr_cell_27_613_end:
__sbr_cell_27_614:
    pop r14
__sbr_cell_27_614_end:
__sbr_cell_27_615:
    pop r15
__sbr_cell_27_615_end:
__sbr_cell_27_616:
    pop rbp
__sbr_cell_27_616_end:
__sbr_cell_27_617:
    vzeroupper
__sbr_cell_27_617_end:
read_sbr_envelope.done:
__sbr_cell_27_618:
    ret
__sbr_cell_27_618_end:
read_sbr_envelope.L60b8:
__sbr_cell_27_619:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_619_end:
read_sbr_envelope.L60bd:
__sbr_cell_27_620:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_620_end:
read_sbr_envelope.L60c2:
__sbr_cell_27_621:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_621_end:
read_sbr_envelope.L60c7:
__sbr_cell_27_622:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_622_end:
read_sbr_envelope.L60cc:
__sbr_cell_27_623:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_623_end:
read_sbr_envelope.L60d1:
__sbr_cell_27_624:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_624_end:
read_sbr_envelope.L60d6:
__sbr_cell_27_625:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_625_end:
read_sbr_envelope.L60db:
__sbr_cell_27_626:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_626_end:
read_sbr_envelope.L60e0:
__sbr_cell_27_627:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_627_end:
read_sbr_envelope.L60e5:
__sbr_cell_27_628:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_628_end:
read_sbr_envelope.L60ea:
__sbr_cell_27_629:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_629_end:
read_sbr_envelope.L60ef:
__sbr_cell_27_630:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_630_end:
read_sbr_envelope.L60f4:
__sbr_cell_27_631:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_631_end:
read_sbr_envelope.L60f9:
__sbr_cell_27_632:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_27_632_end:
__sbr_cell_27_633:
    int3
__sbr_cell_27_633_end:
__sbr_cell_27_634:
    int3
__sbr_cell_27_634_end:
.size read_sbr_envelope, .-read_sbr_envelope
.section .text.read_sbr_grid,"ax",@progbits
.globl read_sbr_grid
.type read_sbr_grid,@function
read_sbr_grid:
__sbr_cell_28_0:
    push rbp
__sbr_cell_28_0_end:
__sbr_cell_28_1:
    mov rbp, rsp
__sbr_cell_28_1_end:
__sbr_cell_28_2:
    push r15
__sbr_cell_28_2_end:
__sbr_cell_28_3:
    push r14
__sbr_cell_28_3_end:
__sbr_cell_28_4:
    push r12
__sbr_cell_28_4_end:
__sbr_cell_28_5:
    push rbx
__sbr_cell_28_5_end:
read_sbr_grid.L440b:
__sbr_cell_28_6:
    mov r14d, DWORD PTR [rcx+8]
__sbr_cell_28_6_end:
__sbr_cell_28_7:
    cmp r14, 9
__sbr_cell_28_7_end:
__sbr_cell_28_8:
    jae read_sbr_grid.L50e3
__sbr_cell_28_8_end:
read_sbr_grid.L4419:
__sbr_cell_28_9:
    mov rbx, rcx
__sbr_cell_28_9_end:
__sbr_cell_28_10:
    movzx eax, BYTE PTR [rcx+r14*1+12]
__sbr_cell_28_10_end:
read_sbr_grid.L4422:
__sbr_cell_28_11:
    mov BYTE PTR [rcx+12], al
__sbr_cell_28_11_end:
__sbr_cell_28_12:
    mov eax, DWORD PTR [rsi+36]
__sbr_cell_28_12_end:
__sbr_cell_28_13:
    mov DWORD PTR [rcx+100], eax
__sbr_cell_28_13_end:
read_sbr_grid.L442b:
__sbr_cell_28_14:
    movzx eax, BYTE PTR [rcx+r14*1+88732]
__sbr_cell_28_14_end:
read_sbr_grid.L4434:
__sbr_cell_28_15:
    mov BYTE PTR [rcx+88741], al
__sbr_cell_28_15_end:
read_sbr_grid.L443a:
__sbr_cell_28_16:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_16_end:
__sbr_cell_28_17:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_28_17_end:
__sbr_cell_28_18:
    mov ecx, r9d
__sbr_cell_28_18_end:
__sbr_cell_28_19:
    shr ecx, 3
__sbr_cell_28_19_end:
__sbr_cell_28_20:
    mov r15d, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_20_end:
__sbr_cell_28_21:
    bswap r15d
__sbr_cell_28_21_end:
__sbr_cell_28_22:
    mov ecx, r9d
__sbr_cell_28_22_end:
__sbr_cell_28_23:
    and cl, 7
__sbr_cell_28_23_end:
__sbr_cell_28_24:
    shl r15d, cl
__sbr_cell_28_24_end:
__sbr_cell_28_25:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_28_25_end:
__sbr_cell_28_26:
    shr r15d, 30
__sbr_cell_28_26_end:
__sbr_cell_28_27:
    add r9d, 2
__sbr_cell_28_27_end:
__sbr_cell_28_28:
    cmp r8d, r9d
__sbr_cell_28_28_end:
__sbr_cell_28_29:
    cmovb r9d, r8d
__sbr_cell_28_29_end:
__sbr_cell_28_30:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_30_end:
__sbr_cell_28_31:
    cmp r15d, 3
__sbr_cell_28_31_end:
__sbr_cell_28_32:
    ja read_sbr_grid.L4de0
__sbr_cell_28_32_end:
read_sbr_grid.L4478:
__sbr_cell_28_33:
    mov ecx, r15d
__sbr_cell_28_33_end:
__sbr_cell_28_34:
    lea r10, [rip+read_sbr_grid_jt]
__sbr_cell_28_34_end:
__sbr_cell_28_35:
    movsxd rcx, DWORD PTR [r10+rcx*4+0]
__sbr_cell_28_35_end:
__sbr_cell_28_36:
    add rcx, r10
__sbr_cell_28_36_end:
__sbr_cell_28_37:
    jmp rcx
__sbr_cell_28_37_end:
read_sbr_grid.L448b:
__sbr_cell_28_38:
    mov ecx, r9d
__sbr_cell_28_38_end:
__sbr_cell_28_39:
    shr ecx, 3
__sbr_cell_28_39_end:
__sbr_cell_28_40:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_40_end:
__sbr_cell_28_41:
    bswap eax
__sbr_cell_28_41_end:
__sbr_cell_28_42:
    mov ecx, r9d
__sbr_cell_28_42_end:
__sbr_cell_28_43:
    and cl, 7
__sbr_cell_28_43_end:
__sbr_cell_28_44:
    shl eax, cl
__sbr_cell_28_44_end:
__sbr_cell_28_45:
    shr eax, 30
__sbr_cell_28_45_end:
__sbr_cell_28_46:
    add r9d, 2
__sbr_cell_28_46_end:
__sbr_cell_28_47:
    cmp r8d, r9d
__sbr_cell_28_47_end:
__sbr_cell_28_48:
    cmovb r9d, r8d
__sbr_cell_28_48_end:
__sbr_cell_28_49:
    mov r8d, 1
__sbr_cell_28_49_end:
__sbr_cell_28_50:
    mov ecx, eax
__sbr_cell_28_50_end:
__sbr_cell_28_51:
    shl r8, cl
__sbr_cell_28_51_end:
__sbr_cell_28_52:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_52_end:
__sbr_cell_28_53:
    xor ecx, ecx
__sbr_cell_28_53_end:
__sbr_cell_28_54:
    cmp DWORD PTR [rsi+16], 0
__sbr_cell_28_54_end:
__sbr_cell_28_55:
    setne cl
__sbr_cell_28_55_end:
__sbr_cell_28_56:
    lea ecx, [rcx+rcx*2+0]
__sbr_cell_28_56_end:
__sbr_cell_28_57:
    add ecx, 5
__sbr_cell_28_57_end:
__sbr_cell_28_58:
    cmp r8d, ecx
__sbr_cell_28_58_end:
__sbr_cell_28_59:
    jle read_sbr_grid.L4cb0
__sbr_cell_28_59_end:
__sbr_cell_28_60:
    mov rdi, QWORD PTR [rdi+8]
__sbr_cell_28_60_end:
__sbr_cell_28_61:
    lea rdx, [rip+L_str_25]
__sbr_cell_28_61_end:
__sbr_cell_28_62:
    jmp read_sbr_grid.L4ec4
__sbr_cell_28_62_end:
read_sbr_grid.L44e3:
__sbr_cell_28_63:
    mov ecx, r9d
__sbr_cell_28_63_end:
__sbr_cell_28_64:
    shr ecx, 3
__sbr_cell_28_64_end:
__sbr_cell_28_65:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_65_end:
__sbr_cell_28_66:
    bswap eax
__sbr_cell_28_66_end:
__sbr_cell_28_67:
    mov ecx, r9d
__sbr_cell_28_67_end:
__sbr_cell_28_68:
    and cl, 7
__sbr_cell_28_68_end:
__sbr_cell_28_69:
    shl eax, cl
__sbr_cell_28_69_end:
__sbr_cell_28_70:
    shr eax, 30
__sbr_cell_28_70_end:
__sbr_cell_28_71:
    add r9d, 2
__sbr_cell_28_71_end:
__sbr_cell_28_72:
    cmp r8d, r9d
__sbr_cell_28_72_end:
__sbr_cell_28_73:
    cmovb r9d, r8d
__sbr_cell_28_73_end:
__sbr_cell_28_74:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_74_end:
__sbr_cell_28_75:
    mov BYTE PTR [rbx+88732], al
__sbr_cell_28_75_end:
read_sbr_grid.L450e:
__sbr_cell_28_76:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_28_76_end:
__sbr_cell_28_77:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_28_77_end:
__sbr_cell_28_78:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_28_78_end:
__sbr_cell_28_79:
    mov ecx, esi
__sbr_cell_28_79_end:
__sbr_cell_28_80:
    shr ecx, 3
__sbr_cell_28_80_end:
__sbr_cell_28_81:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_81_end:
__sbr_cell_28_82:
    bswap eax
__sbr_cell_28_82_end:
__sbr_cell_28_83:
    mov ecx, esi
__sbr_cell_28_83_end:
__sbr_cell_28_84:
    and cl, 7
__sbr_cell_28_84_end:
__sbr_cell_28_85:
    shl eax, cl
__sbr_cell_28_85_end:
__sbr_cell_28_86:
    shr eax, 30
__sbr_cell_28_86_end:
__sbr_cell_28_87:
    add esi, 2
__sbr_cell_28_87_end:
__sbr_cell_28_88:
    cmp r8d, esi
__sbr_cell_28_88_end:
__sbr_cell_28_89:
    cmovb esi, r8d
__sbr_cell_28_89_end:
__sbr_cell_28_90:
    mov DWORD PTR [rdx+8], esi
__sbr_cell_28_90_end:
read_sbr_grid.L4539:
__sbr_cell_28_91:
    lea ecx, [rax+1]
__sbr_cell_28_91_end:
__sbr_cell_28_92:
    mov DWORD PTR [rbx+8], ecx
__sbr_cell_28_92_end:
__sbr_cell_28_93:
    cmp ecx, 9
__sbr_cell_28_93_end:
__sbr_cell_28_94:
    jae read_sbr_grid.L5118
__sbr_cell_28_94_end:
read_sbr_grid.L4548:
__sbr_cell_28_95:
    mov esi, ecx
__sbr_cell_28_95_end:
__sbr_cell_28_96:
    mov BYTE PTR [rbx+rsi*1+88732], 16
__sbr_cell_28_96_end:
__sbr_cell_28_97:
    test eax, eax
__sbr_cell_28_97_end:
__sbr_cell_28_98:
    jle read_sbr_grid.L45cb
__sbr_cell_28_98_end:
read_sbr_grid.L4556:
__sbr_cell_28_99:
    mov eax, eax
__sbr_cell_28_99_end:
__sbr_cell_28_100:
    movzx esi, BYTE PTR [rbx+88732]
__sbr_cell_28_100_end:
__sbr_cell_28_101:
    xor r8d, r8d
__sbr_cell_28_101_end:
__sbr_cell_28_102:
    .nops 1
__sbr_cell_28_102_end:
read_sbr_grid.L4570:
__sbr_cell_28_103:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_103_end:
__sbr_cell_28_104:
    mov r10d, DWORD PTR [rdx+16]
__sbr_cell_28_104_end:
__sbr_cell_28_105:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_105_end:
__sbr_cell_28_106:
    mov r11d, r9d
__sbr_cell_28_106_end:
__sbr_cell_28_107:
    shr r11d, 3
__sbr_cell_28_107_end:
__sbr_cell_28_108:
    mov r11d, DWORD PTR [rcx+r11*1+0]
__sbr_cell_28_108_end:
__sbr_cell_28_109:
    bswap r11d
__sbr_cell_28_109_end:
__sbr_cell_28_110:
    mov ecx, r9d
__sbr_cell_28_110_end:
__sbr_cell_28_111:
    and cl, 7
__sbr_cell_28_111_end:
__sbr_cell_28_112:
    shl r11d, cl
__sbr_cell_28_112_end:
__sbr_cell_28_113:
    shr r11d, 30
__sbr_cell_28_113_end:
__sbr_cell_28_114:
    add r9d, 2
__sbr_cell_28_114_end:
__sbr_cell_28_115:
    cmp r10d, r9d
__sbr_cell_28_115_end:
__sbr_cell_28_116:
    cmovb r9d, r10d
__sbr_cell_28_116_end:
__sbr_cell_28_117:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_117_end:
read_sbr_grid.L45a5:
__sbr_cell_28_118:
    add r11b, r11b
__sbr_cell_28_118_end:
__sbr_cell_28_119:
    add sil, r11b
__sbr_cell_28_119_end:
__sbr_cell_28_120:
    add sil, 2
__sbr_cell_28_120_end:
__sbr_cell_28_121:
    mov BYTE PTR [rbx+r8*1+88733], sil
__sbr_cell_28_121_end:
__sbr_cell_28_122:
    inc r8
__sbr_cell_28_122_end:
__sbr_cell_28_123:
    cmp rax, r8
__sbr_cell_28_123_end:
__sbr_cell_28_124:
    jne read_sbr_grid.L4570
__sbr_cell_28_124_end:
read_sbr_grid.L45bf:
__sbr_cell_28_125:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_28_125_end:
__sbr_cell_28_126:
    cmp ecx, 6
__sbr_cell_28_126_end:
__sbr_cell_28_127:
    jae read_sbr_grid.L5113
__sbr_cell_28_127_end:
read_sbr_grid.L45cb:
__sbr_cell_28_128:
    mov eax, ecx
__sbr_cell_28_128_end:
__sbr_cell_28_129:
    lea rcx, [rip+ceil_log2]
__sbr_cell_28_129_end:
__sbr_cell_28_130:
    movsx eax, BYTE PTR [rax+rcx*1+0]
__sbr_cell_28_130_end:
read_sbr_grid.L45d8:
__sbr_cell_28_131:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_28_131_end:
__sbr_cell_28_132:
    mov r9d, DWORD PTR [rdx+16]
__sbr_cell_28_132_end:
__sbr_cell_28_133:
    mov r8d, esi
__sbr_cell_28_133_end:
__sbr_cell_28_134:
    mov ecx, esi
__sbr_cell_28_134_end:
__sbr_cell_28_135:
    add esi, eax
__sbr_cell_28_135_end:
__sbr_cell_28_136:
    neg al
__sbr_cell_28_136_end:
__sbr_cell_28_137:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_137_end:
__sbr_cell_28_138:
    shr r8d, 3
__sbr_cell_28_138_end:
__sbr_cell_28_139:
    mov r8d, DWORD PTR [r10+r8*1+0]
__sbr_cell_28_139_end:
__sbr_cell_28_140:
    bswap r8d
__sbr_cell_28_140_end:
__sbr_cell_28_141:
    and cl, 7
__sbr_cell_28_141_end:
__sbr_cell_28_142:
    shl r8d, cl
__sbr_cell_28_142_end:
__sbr_cell_28_143:
    mov ecx, eax
__sbr_cell_28_143_end:
__sbr_cell_28_144:
    shr r8d, cl
__sbr_cell_28_144_end:
__sbr_cell_28_145:
    cmp r9d, esi
__sbr_cell_28_145_end:
__sbr_cell_28_146:
    cmovb esi, r9d
__sbr_cell_28_146_end:
__sbr_cell_28_147:
    mov DWORD PTR [rdx+8], esi
__sbr_cell_28_147_end:
read_sbr_grid.L460b:
__sbr_cell_28_148:
    movsxd rsi, DWORD PTR [rbx+8]
__sbr_cell_28_148_end:
__sbr_cell_28_149:
    test rsi, rsi
__sbr_cell_28_149_end:
__sbr_cell_28_150:
    jle read_sbr_grid.L4ea2
__sbr_cell_28_150_end:
__sbr_cell_28_151:
    cmp esi, 1
__sbr_cell_28_151_end:
__sbr_cell_28_152:
    je read_sbr_grid.L4ca9
__sbr_cell_28_152_end:
read_sbr_grid.L4621:
__sbr_cell_28_153:
    mov r9d, esi
__sbr_cell_28_153_end:
__sbr_cell_28_154:
    and r9d, 2147483646
__sbr_cell_28_154_end:
__sbr_cell_28_155:
    xor eax, eax
__sbr_cell_28_155_end:
__sbr_cell_28_156:
    .nops 1
__sbr_cell_28_156_end:
read_sbr_grid.L4630:
__sbr_cell_28_157:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_157_end:
__sbr_cell_28_158:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_158_end:
__sbr_cell_28_159:
    mov r11d, ecx
__sbr_cell_28_159_end:
__sbr_cell_28_160:
    shr r11d, 3
__sbr_cell_28_160_end:
__sbr_cell_28_161:
    xor r12d, r12d
__sbr_cell_28_161_end:
__sbr_cell_28_162:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_162_end:
__sbr_cell_28_163:
    setl r12b
__sbr_cell_28_163_end:
__sbr_cell_28_164:
    add r12d, ecx
__sbr_cell_28_164_end:
__sbr_cell_28_165:
    movzx r10d, BYTE PTR [r10+r11*1+0]
__sbr_cell_28_165_end:
__sbr_cell_28_166:
    and cl, 7
__sbr_cell_28_166_end:
__sbr_cell_28_167:
    shl r10d, cl
__sbr_cell_28_167_end:
__sbr_cell_28_168:
    mov DWORD PTR [rdx+8], r12d
__sbr_cell_28_168_end:
__sbr_cell_28_169:
    shr r10b, 7
__sbr_cell_28_169_end:
__sbr_cell_28_170:
    mov BYTE PTR [rbx+rax*1+13], r10b
__sbr_cell_28_170_end:
read_sbr_grid.L4662:
__sbr_cell_28_171:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_171_end:
__sbr_cell_28_172:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_172_end:
__sbr_cell_28_173:
    mov r11d, ecx
__sbr_cell_28_173_end:
__sbr_cell_28_174:
    shr r11d, 3
__sbr_cell_28_174_end:
__sbr_cell_28_175:
    xor r12d, r12d
__sbr_cell_28_175_end:
__sbr_cell_28_176:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_176_end:
__sbr_cell_28_177:
    setl r12b
__sbr_cell_28_177_end:
__sbr_cell_28_178:
    add r12d, ecx
__sbr_cell_28_178_end:
__sbr_cell_28_179:
    movzx r10d, BYTE PTR [r10+r11*1+0]
__sbr_cell_28_179_end:
__sbr_cell_28_180:
    and cl, 7
__sbr_cell_28_180_end:
__sbr_cell_28_181:
    shl r10d, cl
__sbr_cell_28_181_end:
__sbr_cell_28_182:
    mov DWORD PTR [rdx+8], r12d
__sbr_cell_28_182_end:
__sbr_cell_28_183:
    shr r10b, 7
__sbr_cell_28_183_end:
__sbr_cell_28_184:
    mov BYTE PTR [rbx+rax*1+14], r10b
__sbr_cell_28_184_end:
read_sbr_grid.L4694:
__sbr_cell_28_185:
    add rax, 2
__sbr_cell_28_185_end:
__sbr_cell_28_186:
    cmp r9, rax
__sbr_cell_28_186_end:
__sbr_cell_28_187:
    jne read_sbr_grid.L4630
__sbr_cell_28_187_end:
__sbr_cell_28_188:
    jmp read_sbr_grid.L4e6d
__sbr_cell_28_188_end:
read_sbr_grid.L46a2:
__sbr_cell_28_189:
    mov ecx, r9d
__sbr_cell_28_189_end:
__sbr_cell_28_190:
    shr ecx, 3
__sbr_cell_28_190_end:
__sbr_cell_28_191:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_191_end:
__sbr_cell_28_192:
    bswap eax
__sbr_cell_28_192_end:
__sbr_cell_28_193:
    mov ecx, r9d
__sbr_cell_28_193_end:
__sbr_cell_28_194:
    and cl, 7
__sbr_cell_28_194_end:
__sbr_cell_28_195:
    shl eax, cl
__sbr_cell_28_195_end:
__sbr_cell_28_196:
    shr eax, 30
__sbr_cell_28_196_end:
__sbr_cell_28_197:
    add r9d, 2
__sbr_cell_28_197_end:
__sbr_cell_28_198:
    cmp r8d, r9d
__sbr_cell_28_198_end:
__sbr_cell_28_199:
    cmovb r9d, r8d
__sbr_cell_28_199_end:
__sbr_cell_28_200:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_200_end:
__sbr_cell_28_201:
    mov BYTE PTR [rbx+88732], al
__sbr_cell_28_201_end:
read_sbr_grid.L46cd:
__sbr_cell_28_202:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_202_end:
__sbr_cell_28_203:
    mov r10d, DWORD PTR [rdx+16]
__sbr_cell_28_203_end:
__sbr_cell_28_204:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_28_204_end:
__sbr_cell_28_205:
    mov ecx, r9d
__sbr_cell_28_205_end:
__sbr_cell_28_206:
    shr ecx, 3
__sbr_cell_28_206_end:
__sbr_cell_28_207:
    mov r8d, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_207_end:
__sbr_cell_28_208:
    bswap r8d
__sbr_cell_28_208_end:
__sbr_cell_28_209:
    mov ecx, r9d
__sbr_cell_28_209_end:
__sbr_cell_28_210:
    and cl, 7
__sbr_cell_28_210_end:
__sbr_cell_28_211:
    shl r8d, cl
__sbr_cell_28_211_end:
__sbr_cell_28_212:
    shr r8d, 30
__sbr_cell_28_212_end:
__sbr_cell_28_213:
    add r9d, 2
__sbr_cell_28_213_end:
__sbr_cell_28_214:
    cmp r10d, r9d
__sbr_cell_28_214_end:
__sbr_cell_28_215:
    cmovb r9d, r10d
__sbr_cell_28_215_end:
__sbr_cell_28_216:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_216_end:
read_sbr_grid.L4701:
__sbr_cell_28_217:
    mov ecx, r9d
__sbr_cell_28_217_end:
__sbr_cell_28_218:
    shr ecx, 3
__sbr_cell_28_218_end:
__sbr_cell_28_219:
    mov esi, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_219_end:
__sbr_cell_28_220:
    bswap esi
__sbr_cell_28_220_end:
__sbr_cell_28_221:
    mov ecx, r9d
__sbr_cell_28_221_end:
__sbr_cell_28_222:
    and cl, 7
__sbr_cell_28_222_end:
__sbr_cell_28_223:
    shl esi, cl
__sbr_cell_28_223_end:
__sbr_cell_28_224:
    shr esi, 30
__sbr_cell_28_224_end:
__sbr_cell_28_225:
    add r9d, 2
__sbr_cell_28_225_end:
__sbr_cell_28_226:
    cmp r10d, r9d
__sbr_cell_28_226_end:
__sbr_cell_28_227:
    cmovb r9d, r10d
__sbr_cell_28_227_end:
__sbr_cell_28_228:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_228_end:
read_sbr_grid.L4726:
__sbr_cell_28_229:
    mov ecx, r9d
__sbr_cell_28_229_end:
__sbr_cell_28_230:
    shr ecx, 3
__sbr_cell_28_230_end:
__sbr_cell_28_231:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_231_end:
__sbr_cell_28_232:
    bswap eax
__sbr_cell_28_232_end:
__sbr_cell_28_233:
    mov ecx, r9d
__sbr_cell_28_233_end:
__sbr_cell_28_234:
    and cl, 7
__sbr_cell_28_234_end:
__sbr_cell_28_235:
    shl eax, cl
__sbr_cell_28_235_end:
__sbr_cell_28_236:
    shr eax, 30
__sbr_cell_28_236_end:
__sbr_cell_28_237:
    add r9d, 2
__sbr_cell_28_237_end:
__sbr_cell_28_238:
    cmp r10d, r9d
__sbr_cell_28_238_end:
__sbr_cell_28_239:
    cmovb r9d, r10d
__sbr_cell_28_239_end:
__sbr_cell_28_240:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_240_end:
read_sbr_grid.L474b:
__sbr_cell_28_241:
    lea r9d, [rax+rsi*1+0]
__sbr_cell_28_241_end:
__sbr_cell_28_242:
    lea ecx, [rax+rsi*1+0]
__sbr_cell_28_242_end:
__sbr_cell_28_243:
    inc ecx
__sbr_cell_28_243_end:
__sbr_cell_28_244:
    cmp r9d, 5
__sbr_cell_28_244_end:
__sbr_cell_28_245:
    jl read_sbr_grid.L4925
__sbr_cell_28_245_end:
__sbr_cell_28_246:
    mov rdi, QWORD PTR [rdi+8]
__sbr_cell_28_246_end:
__sbr_cell_28_247:
    lea rdx, [rip+L_str_26]
__sbr_cell_28_247_end:
__sbr_cell_28_248:
    mov esi, 16
__sbr_cell_28_248_end:
__sbr_cell_28_249:
    jmp read_sbr_grid.L4ecc
__sbr_cell_28_249_end:
read_sbr_grid.L4773:
__sbr_cell_28_250:
    mov ecx, r9d
__sbr_cell_28_250_end:
__sbr_cell_28_251:
    shr ecx, 3
__sbr_cell_28_251_end:
__sbr_cell_28_252:
    mov esi, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_252_end:
__sbr_cell_28_253:
    bswap esi
__sbr_cell_28_253_end:
__sbr_cell_28_254:
    mov ecx, r9d
__sbr_cell_28_254_end:
__sbr_cell_28_255:
    and cl, 7
__sbr_cell_28_255_end:
__sbr_cell_28_256:
    shl esi, cl
__sbr_cell_28_256_end:
__sbr_cell_28_257:
    shr esi, 30
__sbr_cell_28_257_end:
__sbr_cell_28_258:
    add r9d, 2
__sbr_cell_28_258_end:
__sbr_cell_28_259:
    cmp r8d, r9d
__sbr_cell_28_259_end:
__sbr_cell_28_260:
    cmovb r9d, r8d
__sbr_cell_28_260_end:
__sbr_cell_28_261:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_261_end:
read_sbr_grid.L4798:
__sbr_cell_28_262:
    mov ecx, r9d
__sbr_cell_28_262_end:
__sbr_cell_28_263:
    shr ecx, 3
__sbr_cell_28_263_end:
__sbr_cell_28_264:
    mov eax, DWORD PTR [rax+rcx*1+0]
__sbr_cell_28_264_end:
__sbr_cell_28_265:
    bswap eax
__sbr_cell_28_265_end:
__sbr_cell_28_266:
    mov ecx, r9d
__sbr_cell_28_266_end:
__sbr_cell_28_267:
    and cl, 7
__sbr_cell_28_267_end:
__sbr_cell_28_268:
    shl eax, cl
__sbr_cell_28_268_end:
__sbr_cell_28_269:
    shr eax, 30
__sbr_cell_28_269_end:
__sbr_cell_28_270:
    add r9d, 2
__sbr_cell_28_270_end:
__sbr_cell_28_271:
    cmp r8d, r9d
__sbr_cell_28_271_end:
__sbr_cell_28_272:
    cmovb r9d, r8d
__sbr_cell_28_272_end:
__sbr_cell_28_273:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_273_end:
read_sbr_grid.L47bd:
__sbr_cell_28_274:
    lea ecx, [rax+1]
__sbr_cell_28_274_end:
__sbr_cell_28_275:
    mov DWORD PTR [rbx+8], ecx
__sbr_cell_28_275_end:
__sbr_cell_28_276:
    mov BYTE PTR [rbx+88732], 0
__sbr_cell_28_276_end:
__sbr_cell_28_277:
    cmp ecx, 9
__sbr_cell_28_277_end:
__sbr_cell_28_278:
    jae read_sbr_grid.L511d
__sbr_cell_28_278_end:
read_sbr_grid.L47d3:
__sbr_cell_28_279:
    mov r8d, ecx
__sbr_cell_28_279_end:
__sbr_cell_28_280:
    add sil, 16
__sbr_cell_28_280_end:
__sbr_cell_28_281:
    mov BYTE PTR [rbx+r8*1+88732], sil
__sbr_cell_28_281_end:
__sbr_cell_28_282:
    test eax, eax
__sbr_cell_28_282_end:
__sbr_cell_28_283:
    jle read_sbr_grid.L4873
__sbr_cell_28_283_end:
read_sbr_grid.L47ea:
__sbr_cell_28_284:
    neg eax
__sbr_cell_28_284_end:
__sbr_cell_28_285:
    xor esi, esi
__sbr_cell_28_285_end:
__sbr_cell_28_286:
    .nops 1
__sbr_cell_28_286_end:
read_sbr_grid.L47f0:
__sbr_cell_28_287:
    add ecx, esi
__sbr_cell_28_287_end:
__sbr_cell_28_288:
    cmp ecx, 9
__sbr_cell_28_288_end:
__sbr_cell_28_289:
    jae read_sbr_grid.L50cf
__sbr_cell_28_289_end:
read_sbr_grid.L47fb:
__sbr_cell_28_290:
    mov ecx, ecx
__sbr_cell_28_290_end:
__sbr_cell_28_291:
    movzx r8d, BYTE PTR [rbx+rcx*1+88732]
__sbr_cell_28_291_end:
read_sbr_grid.L4806:
__sbr_cell_28_292:
    mov r10d, DWORD PTR [rdx+8]
__sbr_cell_28_292_end:
__sbr_cell_28_293:
    mov r11d, DWORD PTR [rdx+16]
__sbr_cell_28_293_end:
__sbr_cell_28_294:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_294_end:
__sbr_cell_28_295:
    mov r9d, r10d
__sbr_cell_28_295_end:
__sbr_cell_28_296:
    shr r9d, 3
__sbr_cell_28_296_end:
__sbr_cell_28_297:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_28_297_end:
__sbr_cell_28_298:
    bswap r9d
__sbr_cell_28_298_end:
__sbr_cell_28_299:
    mov ecx, r10d
__sbr_cell_28_299_end:
__sbr_cell_28_300:
    and cl, 7
__sbr_cell_28_300_end:
__sbr_cell_28_301:
    shl r9d, cl
__sbr_cell_28_301_end:
__sbr_cell_28_302:
    shr r9d, 30
__sbr_cell_28_302_end:
__sbr_cell_28_303:
    add r10d, 2
__sbr_cell_28_303_end:
__sbr_cell_28_304:
    cmp r11d, r10d
__sbr_cell_28_304_end:
__sbr_cell_28_305:
    cmovb r10d, r11d
__sbr_cell_28_305_end:
__sbr_cell_28_306:
    mov DWORD PTR [rdx+8], r10d
__sbr_cell_28_306_end:
read_sbr_grid.L483b:
__sbr_cell_28_307:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_28_307_end:
__sbr_cell_28_308:
    lea r10d, [rsi+rcx*1+0]
__sbr_cell_28_308_end:
__sbr_cell_28_309:
    dec r10d
__sbr_cell_28_309_end:
__sbr_cell_28_310:
    cmp r10d, 9
__sbr_cell_28_310_end:
__sbr_cell_28_311:
    jae read_sbr_grid.L50ca
__sbr_cell_28_311_end:
read_sbr_grid.L484f:
__sbr_cell_28_312:
    mov r10d, r10d
__sbr_cell_28_312_end:
__sbr_cell_28_313:
    add r9b, r9b
__sbr_cell_28_313_end:
__sbr_cell_28_314:
    sub r8b, r9b
__sbr_cell_28_314_end:
__sbr_cell_28_315:
    add r8b, 254
__sbr_cell_28_315_end:
__sbr_cell_28_316:
    mov BYTE PTR [rbx+r10*1+88732], r8b
__sbr_cell_28_316_end:
__sbr_cell_28_317:
    dec esi
__sbr_cell_28_317_end:
__sbr_cell_28_318:
    cmp eax, esi
__sbr_cell_28_318_end:
__sbr_cell_28_319:
    jne read_sbr_grid.L47f0
__sbr_cell_28_319_end:
read_sbr_grid.L486a:
__sbr_cell_28_320:
    cmp ecx, 6
__sbr_cell_28_320_end:
__sbr_cell_28_321:
    jae read_sbr_grid.L5122
__sbr_cell_28_321_end:
read_sbr_grid.L4873:
__sbr_cell_28_322:
    mov eax, ecx
__sbr_cell_28_322_end:
__sbr_cell_28_323:
    lea rcx, [rip+ceil_log2]
__sbr_cell_28_323_end:
__sbr_cell_28_324:
    movsx eax, BYTE PTR [rax+rcx*1+0]
__sbr_cell_28_324_end:
read_sbr_grid.L4880:
__sbr_cell_28_325:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_28_325_end:
__sbr_cell_28_326:
    mov r9d, DWORD PTR [rdx+16]
__sbr_cell_28_326_end:
__sbr_cell_28_327:
    mov r8d, esi
__sbr_cell_28_327_end:
__sbr_cell_28_328:
    mov ecx, esi
__sbr_cell_28_328_end:
__sbr_cell_28_329:
    add esi, eax
__sbr_cell_28_329_end:
__sbr_cell_28_330:
    neg al
__sbr_cell_28_330_end:
__sbr_cell_28_331:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_331_end:
__sbr_cell_28_332:
    shr r8d, 3
__sbr_cell_28_332_end:
__sbr_cell_28_333:
    mov r8d, DWORD PTR [r10+r8*1+0]
__sbr_cell_28_333_end:
__sbr_cell_28_334:
    bswap r8d
__sbr_cell_28_334_end:
__sbr_cell_28_335:
    and cl, 7
__sbr_cell_28_335_end:
__sbr_cell_28_336:
    shl r8d, cl
__sbr_cell_28_336_end:
__sbr_cell_28_337:
    mov ecx, eax
__sbr_cell_28_337_end:
__sbr_cell_28_338:
    shr r8d, cl
__sbr_cell_28_338_end:
__sbr_cell_28_339:
    cmp r9d, esi
__sbr_cell_28_339_end:
__sbr_cell_28_340:
    cmovb esi, r9d
__sbr_cell_28_340_end:
__sbr_cell_28_341:
    mov DWORD PTR [rdx+8], esi
__sbr_cell_28_341_end:
read_sbr_grid.L48b3:
__sbr_cell_28_342:
    cmp DWORD PTR [rbx+8], 0
__sbr_cell_28_342_end:
__sbr_cell_28_343:
    je read_sbr_grid.L4ea2
__sbr_cell_28_343_end:
__sbr_cell_28_344:
    xor eax, eax
__sbr_cell_28_344_end:
__sbr_cell_28_345:
    xor esi, esi
__sbr_cell_28_345_end:
__sbr_cell_28_346:
    .nops 1
__sbr_cell_28_346_end:
read_sbr_grid.L48d0:
__sbr_cell_28_347:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_347_end:
__sbr_cell_28_348:
    mov r9, QWORD PTR [rdx+0]
__sbr_cell_28_348_end:
__sbr_cell_28_349:
    mov r10d, ecx
__sbr_cell_28_349_end:
__sbr_cell_28_350:
    shr r10d, 3
__sbr_cell_28_350_end:
__sbr_cell_28_351:
    movzx r9d, BYTE PTR [r9+r10*1+0]
__sbr_cell_28_351_end:
__sbr_cell_28_352:
    xor r10d, r10d
__sbr_cell_28_352_end:
__sbr_cell_28_353:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_353_end:
__sbr_cell_28_354:
    setl r10b
__sbr_cell_28_354_end:
__sbr_cell_28_355:
    add r10d, ecx
__sbr_cell_28_355_end:
__sbr_cell_28_356:
    mov DWORD PTR [rdx+8], r10d
__sbr_cell_28_356_end:
read_sbr_grid.L48f3:
__sbr_cell_28_357:
    mov r10d, DWORD PTR [rbx+8]
__sbr_cell_28_357_end:
__sbr_cell_28_358:
    lea r11d, [rax+r10*1+0]
__sbr_cell_28_358_end:
__sbr_cell_28_359:
    cmp r11d, 9
__sbr_cell_28_359_end:
__sbr_cell_28_360:
    jae read_sbr_grid.L50d4
__sbr_cell_28_360_end:
read_sbr_grid.L4905:
__sbr_cell_28_361:
    and cl, 7
__sbr_cell_28_361_end:
__sbr_cell_28_362:
    shl r9d, cl
__sbr_cell_28_362_end:
__sbr_cell_28_363:
    mov ecx, r11d
__sbr_cell_28_363_end:
__sbr_cell_28_364:
    shr r9b, 7
__sbr_cell_28_364_end:
__sbr_cell_28_365:
    mov BYTE PTR [rbx+rcx*1+12], r9b
__sbr_cell_28_365_end:
__sbr_cell_28_366:
    inc esi
__sbr_cell_28_366_end:
__sbr_cell_28_367:
    dec eax
__sbr_cell_28_367_end:
__sbr_cell_28_368:
    cmp esi, r10d
__sbr_cell_28_368_end:
__sbr_cell_28_369:
    jb read_sbr_grid.L48d0
__sbr_cell_28_369_end:
__sbr_cell_28_370:
    jmp read_sbr_grid.L4ea2
__sbr_cell_28_370_end:
read_sbr_grid.L4925:
__sbr_cell_28_371:
    mov DWORD PTR [rbx+8], ecx
__sbr_cell_28_371_end:
__sbr_cell_28_372:
    cmp ecx, 9
__sbr_cell_28_372_end:
__sbr_cell_28_373:
    jae read_sbr_grid.L5127
__sbr_cell_28_373_end:
__sbr_cell_28_374:
    mov r9d, ecx
__sbr_cell_28_374_end:
__sbr_cell_28_375:
    add r8b, 16
__sbr_cell_28_375_end:
__sbr_cell_28_376:
    mov BYTE PTR [rbx+r9*1+88732], r8b
__sbr_cell_28_376_end:
__sbr_cell_28_377:
    test esi, esi
__sbr_cell_28_377_end:
__sbr_cell_28_378:
    jle read_sbr_grid.L4bbc
__sbr_cell_28_378_end:
read_sbr_grid.L4948:
__sbr_cell_28_379:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_379_end:
__sbr_cell_28_380:
    mov r10d, DWORD PTR [rdx+16]
__sbr_cell_28_380_end:
__sbr_cell_28_381:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_381_end:
__sbr_cell_28_382:
    mov r8d, r9d
__sbr_cell_28_382_end:
__sbr_cell_28_383:
    shr r8d, 3
__sbr_cell_28_383_end:
__sbr_cell_28_384:
    mov r8d, DWORD PTR [rcx+r8*1+0]
__sbr_cell_28_384_end:
__sbr_cell_28_385:
    bswap r8d
__sbr_cell_28_385_end:
__sbr_cell_28_386:
    mov ecx, r9d
__sbr_cell_28_386_end:
__sbr_cell_28_387:
    and cl, 7
__sbr_cell_28_387_end:
__sbr_cell_28_388:
    shl r8d, cl
__sbr_cell_28_388_end:
__sbr_cell_28_389:
    shr r8d, 30
__sbr_cell_28_389_end:
__sbr_cell_28_390:
    add r9d, 2
__sbr_cell_28_390_end:
__sbr_cell_28_391:
    cmp r10d, r9d
__sbr_cell_28_391_end:
__sbr_cell_28_392:
    cmovb r9d, r10d
__sbr_cell_28_392_end:
read_sbr_grid.L4979:
__sbr_cell_28_393:
    add r8b, r8b
__sbr_cell_28_393_end:
__sbr_cell_28_394:
    add r8b, BYTE PTR [rbx+88732]
__sbr_cell_28_394_end:
__sbr_cell_28_395:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_395_end:
__sbr_cell_28_396:
    add r8b, 2
__sbr_cell_28_396_end:
__sbr_cell_28_397:
    mov BYTE PTR [rbx+88733], r8b
__sbr_cell_28_397_end:
__sbr_cell_28_398:
    cmp esi, 1
__sbr_cell_28_398_end:
__sbr_cell_28_399:
    je read_sbr_grid.L4bb9
__sbr_cell_28_399_end:
read_sbr_grid.L499b:
__sbr_cell_28_400:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_400_end:
__sbr_cell_28_401:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_401_end:
__sbr_cell_28_402:
    mov r10d, r9d
__sbr_cell_28_402_end:
__sbr_cell_28_403:
    shr r10d, 3
__sbr_cell_28_403_end:
__sbr_cell_28_404:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_404_end:
__sbr_cell_28_405:
    bswap r10d
__sbr_cell_28_405_end:
__sbr_cell_28_406:
    mov ecx, r9d
__sbr_cell_28_406_end:
__sbr_cell_28_407:
    and cl, 7
__sbr_cell_28_407_end:
__sbr_cell_28_408:
    shl r10d, cl
__sbr_cell_28_408_end:
__sbr_cell_28_409:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_409_end:
__sbr_cell_28_410:
    shr r10d, 30
__sbr_cell_28_410_end:
__sbr_cell_28_411:
    add r9d, 2
__sbr_cell_28_411_end:
__sbr_cell_28_412:
    cmp ecx, r9d
__sbr_cell_28_412_end:
__sbr_cell_28_413:
    cmovb r9d, ecx
__sbr_cell_28_413_end:
__sbr_cell_28_414:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_414_end:
read_sbr_grid.L49cf:
__sbr_cell_28_415:
    add r10b, r10b
__sbr_cell_28_415_end:
__sbr_cell_28_416:
    add r8b, r10b
__sbr_cell_28_416_end:
__sbr_cell_28_417:
    add r8b, 2
__sbr_cell_28_417_end:
__sbr_cell_28_418:
    mov BYTE PTR [rbx+88734], r8b
__sbr_cell_28_418_end:
__sbr_cell_28_419:
    cmp esi, 2
__sbr_cell_28_419_end:
__sbr_cell_28_420:
    je read_sbr_grid.L4bb9
__sbr_cell_28_420_end:
read_sbr_grid.L49e9:
__sbr_cell_28_421:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_421_end:
__sbr_cell_28_422:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_422_end:
__sbr_cell_28_423:
    mov r10d, r9d
__sbr_cell_28_423_end:
__sbr_cell_28_424:
    shr r10d, 3
__sbr_cell_28_424_end:
__sbr_cell_28_425:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_425_end:
__sbr_cell_28_426:
    bswap r10d
__sbr_cell_28_426_end:
__sbr_cell_28_427:
    mov ecx, r9d
__sbr_cell_28_427_end:
__sbr_cell_28_428:
    and cl, 7
__sbr_cell_28_428_end:
__sbr_cell_28_429:
    shl r10d, cl
__sbr_cell_28_429_end:
__sbr_cell_28_430:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_430_end:
__sbr_cell_28_431:
    shr r10d, 30
__sbr_cell_28_431_end:
__sbr_cell_28_432:
    add r9d, 2
__sbr_cell_28_432_end:
__sbr_cell_28_433:
    cmp ecx, r9d
__sbr_cell_28_433_end:
__sbr_cell_28_434:
    cmovb r9d, ecx
__sbr_cell_28_434_end:
__sbr_cell_28_435:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_435_end:
read_sbr_grid.L4a1d:
__sbr_cell_28_436:
    add r10b, r10b
__sbr_cell_28_436_end:
__sbr_cell_28_437:
    add r8b, r10b
__sbr_cell_28_437_end:
__sbr_cell_28_438:
    add r8b, 2
__sbr_cell_28_438_end:
__sbr_cell_28_439:
    mov BYTE PTR [rbx+88735], r8b
__sbr_cell_28_439_end:
__sbr_cell_28_440:
    cmp esi, 3
__sbr_cell_28_440_end:
__sbr_cell_28_441:
    je read_sbr_grid.L4bb9
__sbr_cell_28_441_end:
read_sbr_grid.L4a37:
__sbr_cell_28_442:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_442_end:
__sbr_cell_28_443:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_443_end:
__sbr_cell_28_444:
    mov r10d, r9d
__sbr_cell_28_444_end:
__sbr_cell_28_445:
    shr r10d, 3
__sbr_cell_28_445_end:
__sbr_cell_28_446:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_446_end:
__sbr_cell_28_447:
    bswap r10d
__sbr_cell_28_447_end:
__sbr_cell_28_448:
    mov ecx, r9d
__sbr_cell_28_448_end:
__sbr_cell_28_449:
    and cl, 7
__sbr_cell_28_449_end:
__sbr_cell_28_450:
    shl r10d, cl
__sbr_cell_28_450_end:
__sbr_cell_28_451:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_451_end:
__sbr_cell_28_452:
    shr r10d, 30
__sbr_cell_28_452_end:
__sbr_cell_28_453:
    add r9d, 2
__sbr_cell_28_453_end:
__sbr_cell_28_454:
    cmp ecx, r9d
__sbr_cell_28_454_end:
__sbr_cell_28_455:
    cmovb r9d, ecx
__sbr_cell_28_455_end:
__sbr_cell_28_456:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_456_end:
read_sbr_grid.L4a6b:
__sbr_cell_28_457:
    add r10b, r10b
__sbr_cell_28_457_end:
__sbr_cell_28_458:
    add r8b, r10b
__sbr_cell_28_458_end:
__sbr_cell_28_459:
    add r8b, 2
__sbr_cell_28_459_end:
__sbr_cell_28_460:
    mov BYTE PTR [rbx+88736], r8b
__sbr_cell_28_460_end:
__sbr_cell_28_461:
    cmp esi, 4
__sbr_cell_28_461_end:
__sbr_cell_28_462:
    je read_sbr_grid.L4bb9
__sbr_cell_28_462_end:
read_sbr_grid.L4a85:
__sbr_cell_28_463:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_463_end:
__sbr_cell_28_464:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_464_end:
__sbr_cell_28_465:
    mov r10d, r9d
__sbr_cell_28_465_end:
__sbr_cell_28_466:
    shr r10d, 3
__sbr_cell_28_466_end:
__sbr_cell_28_467:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_467_end:
__sbr_cell_28_468:
    bswap r10d
__sbr_cell_28_468_end:
__sbr_cell_28_469:
    mov ecx, r9d
__sbr_cell_28_469_end:
__sbr_cell_28_470:
    and cl, 7
__sbr_cell_28_470_end:
__sbr_cell_28_471:
    shl r10d, cl
__sbr_cell_28_471_end:
__sbr_cell_28_472:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_472_end:
__sbr_cell_28_473:
    shr r10d, 30
__sbr_cell_28_473_end:
__sbr_cell_28_474:
    add r9d, 2
__sbr_cell_28_474_end:
__sbr_cell_28_475:
    cmp ecx, r9d
__sbr_cell_28_475_end:
__sbr_cell_28_476:
    cmovb r9d, ecx
__sbr_cell_28_476_end:
__sbr_cell_28_477:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_477_end:
read_sbr_grid.L4ab9:
__sbr_cell_28_478:
    add r10b, r10b
__sbr_cell_28_478_end:
__sbr_cell_28_479:
    add r8b, r10b
__sbr_cell_28_479_end:
__sbr_cell_28_480:
    add r8b, 2
__sbr_cell_28_480_end:
__sbr_cell_28_481:
    mov BYTE PTR [rbx+88737], r8b
__sbr_cell_28_481_end:
__sbr_cell_28_482:
    cmp esi, 5
__sbr_cell_28_482_end:
__sbr_cell_28_483:
    je read_sbr_grid.L4bb9
__sbr_cell_28_483_end:
read_sbr_grid.L4ad3:
__sbr_cell_28_484:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_484_end:
__sbr_cell_28_485:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_485_end:
__sbr_cell_28_486:
    mov r10d, r9d
__sbr_cell_28_486_end:
__sbr_cell_28_487:
    shr r10d, 3
__sbr_cell_28_487_end:
__sbr_cell_28_488:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_488_end:
__sbr_cell_28_489:
    bswap r10d
__sbr_cell_28_489_end:
__sbr_cell_28_490:
    mov ecx, r9d
__sbr_cell_28_490_end:
__sbr_cell_28_491:
    and cl, 7
__sbr_cell_28_491_end:
__sbr_cell_28_492:
    shl r10d, cl
__sbr_cell_28_492_end:
__sbr_cell_28_493:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_493_end:
__sbr_cell_28_494:
    shr r10d, 30
__sbr_cell_28_494_end:
__sbr_cell_28_495:
    add r9d, 2
__sbr_cell_28_495_end:
__sbr_cell_28_496:
    cmp ecx, r9d
__sbr_cell_28_496_end:
__sbr_cell_28_497:
    cmovb r9d, ecx
__sbr_cell_28_497_end:
__sbr_cell_28_498:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_498_end:
read_sbr_grid.L4b07:
__sbr_cell_28_499:
    add r10b, r10b
__sbr_cell_28_499_end:
__sbr_cell_28_500:
    add r8b, r10b
__sbr_cell_28_500_end:
__sbr_cell_28_501:
    add r8b, 2
__sbr_cell_28_501_end:
__sbr_cell_28_502:
    mov BYTE PTR [rbx+88738], r8b
__sbr_cell_28_502_end:
__sbr_cell_28_503:
    cmp esi, 6
__sbr_cell_28_503_end:
__sbr_cell_28_504:
    je read_sbr_grid.L4bb9
__sbr_cell_28_504_end:
read_sbr_grid.L4b21:
__sbr_cell_28_505:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_505_end:
__sbr_cell_28_506:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_506_end:
__sbr_cell_28_507:
    mov r10d, r9d
__sbr_cell_28_507_end:
__sbr_cell_28_508:
    shr r10d, 3
__sbr_cell_28_508_end:
__sbr_cell_28_509:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_509_end:
__sbr_cell_28_510:
    bswap r10d
__sbr_cell_28_510_end:
__sbr_cell_28_511:
    mov ecx, r9d
__sbr_cell_28_511_end:
__sbr_cell_28_512:
    and cl, 7
__sbr_cell_28_512_end:
__sbr_cell_28_513:
    shl r10d, cl
__sbr_cell_28_513_end:
__sbr_cell_28_514:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_514_end:
__sbr_cell_28_515:
    shr r10d, 30
__sbr_cell_28_515_end:
__sbr_cell_28_516:
    add r9d, 2
__sbr_cell_28_516_end:
__sbr_cell_28_517:
    cmp ecx, r9d
__sbr_cell_28_517_end:
__sbr_cell_28_518:
    cmovb r9d, ecx
__sbr_cell_28_518_end:
__sbr_cell_28_519:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_519_end:
read_sbr_grid.L4b55:
__sbr_cell_28_520:
    add r10b, r10b
__sbr_cell_28_520_end:
__sbr_cell_28_521:
    add r8b, r10b
__sbr_cell_28_521_end:
__sbr_cell_28_522:
    add r8b, 2
__sbr_cell_28_522_end:
__sbr_cell_28_523:
    mov BYTE PTR [rbx+88739], r8b
__sbr_cell_28_523_end:
__sbr_cell_28_524:
    cmp esi, 7
__sbr_cell_28_524_end:
__sbr_cell_28_525:
    je read_sbr_grid.L4bb9
__sbr_cell_28_525_end:
read_sbr_grid.L4b6b:
__sbr_cell_28_526:
    mov r9d, DWORD PTR [rdx+8]
__sbr_cell_28_526_end:
__sbr_cell_28_527:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_527_end:
__sbr_cell_28_528:
    mov r10d, r9d
__sbr_cell_28_528_end:
__sbr_cell_28_529:
    shr r10d, 3
__sbr_cell_28_529_end:
__sbr_cell_28_530:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_28_530_end:
__sbr_cell_28_531:
    bswap r10d
__sbr_cell_28_531_end:
__sbr_cell_28_532:
    mov ecx, r9d
__sbr_cell_28_532_end:
__sbr_cell_28_533:
    and cl, 7
__sbr_cell_28_533_end:
__sbr_cell_28_534:
    shl r10d, cl
__sbr_cell_28_534_end:
__sbr_cell_28_535:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_535_end:
__sbr_cell_28_536:
    shr r10d, 30
__sbr_cell_28_536_end:
__sbr_cell_28_537:
    add r9d, 2
__sbr_cell_28_537_end:
__sbr_cell_28_538:
    cmp ecx, r9d
__sbr_cell_28_538_end:
__sbr_cell_28_539:
    cmovb r9d, ecx
__sbr_cell_28_539_end:
__sbr_cell_28_540:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_540_end:
read_sbr_grid.L4b9f:
__sbr_cell_28_541:
    add r10b, r10b
__sbr_cell_28_541_end:
__sbr_cell_28_542:
    add r8b, r10b
__sbr_cell_28_542_end:
__sbr_cell_28_543:
    add r8b, 2
__sbr_cell_28_543_end:
__sbr_cell_28_544:
    mov BYTE PTR [rbx+88740], r8b
__sbr_cell_28_544_end:
__sbr_cell_28_545:
    cmp esi, 8
__sbr_cell_28_545_end:
__sbr_cell_28_546:
    jne read_sbr_grid.L513b
__sbr_cell_28_546_end:
read_sbr_grid.L4bb9:
__sbr_cell_28_547:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_28_547_end:
read_sbr_grid.L4bbc:
__sbr_cell_28_548:
    test eax, eax
__sbr_cell_28_548_end:
__sbr_cell_28_549:
    jle read_sbr_grid.L4c4a
__sbr_cell_28_549_end:
__sbr_cell_28_550:
    neg eax
__sbr_cell_28_550_end:
__sbr_cell_28_551:
    xor esi, esi
__sbr_cell_28_551_end:
__sbr_cell_28_552:
    .nops 1
__sbr_cell_28_552_end:
read_sbr_grid.L4bd0:
__sbr_cell_28_553:
    add ecx, esi
__sbr_cell_28_553_end:
__sbr_cell_28_554:
    cmp ecx, 9
__sbr_cell_28_554_end:
__sbr_cell_28_555:
    jae read_sbr_grid.L50de
__sbr_cell_28_555_end:
read_sbr_grid.L4bdb:
__sbr_cell_28_556:
    mov ecx, ecx
__sbr_cell_28_556_end:
__sbr_cell_28_557:
    movzx r8d, BYTE PTR [rbx+rcx*1+88732]
__sbr_cell_28_557_end:
read_sbr_grid.L4be6:
__sbr_cell_28_558:
    mov r10d, DWORD PTR [rdx+8]
__sbr_cell_28_558_end:
__sbr_cell_28_559:
    mov r11d, DWORD PTR [rdx+16]
__sbr_cell_28_559_end:
__sbr_cell_28_560:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_28_560_end:
__sbr_cell_28_561:
    mov r9d, r10d
__sbr_cell_28_561_end:
__sbr_cell_28_562:
    shr r9d, 3
__sbr_cell_28_562_end:
__sbr_cell_28_563:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_28_563_end:
__sbr_cell_28_564:
    bswap r9d
__sbr_cell_28_564_end:
__sbr_cell_28_565:
    mov ecx, r10d
__sbr_cell_28_565_end:
__sbr_cell_28_566:
    and cl, 7
__sbr_cell_28_566_end:
__sbr_cell_28_567:
    shl r9d, cl
__sbr_cell_28_567_end:
__sbr_cell_28_568:
    shr r9d, 30
__sbr_cell_28_568_end:
__sbr_cell_28_569:
    add r10d, 2
__sbr_cell_28_569_end:
__sbr_cell_28_570:
    cmp r11d, r10d
__sbr_cell_28_570_end:
__sbr_cell_28_571:
    cmovb r10d, r11d
__sbr_cell_28_571_end:
__sbr_cell_28_572:
    mov DWORD PTR [rdx+8], r10d
__sbr_cell_28_572_end:
read_sbr_grid.L4c1b:
__sbr_cell_28_573:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_28_573_end:
__sbr_cell_28_574:
    lea r10d, [rsi+rcx*1+0]
__sbr_cell_28_574_end:
__sbr_cell_28_575:
    dec r10d
__sbr_cell_28_575_end:
__sbr_cell_28_576:
    cmp r10d, 9
__sbr_cell_28_576_end:
__sbr_cell_28_577:
    jae read_sbr_grid.L50d9
__sbr_cell_28_577_end:
read_sbr_grid.L4c2f:
__sbr_cell_28_578:
    mov r10d, r10d
__sbr_cell_28_578_end:
__sbr_cell_28_579:
    add r9b, r9b
__sbr_cell_28_579_end:
__sbr_cell_28_580:
    sub r8b, r9b
__sbr_cell_28_580_end:
__sbr_cell_28_581:
    add r8b, 254
__sbr_cell_28_581_end:
__sbr_cell_28_582:
    mov BYTE PTR [rbx+r10*1+88732], r8b
__sbr_cell_28_582_end:
__sbr_cell_28_583:
    dec esi
__sbr_cell_28_583_end:
__sbr_cell_28_584:
    cmp eax, esi
__sbr_cell_28_584_end:
__sbr_cell_28_585:
    jne read_sbr_grid.L4bd0
__sbr_cell_28_585_end:
read_sbr_grid.L4c4a:
__sbr_cell_28_586:
    cmp ecx, 6
__sbr_cell_28_586_end:
__sbr_cell_28_587:
    jae read_sbr_grid.L512c
__sbr_cell_28_587_end:
read_sbr_grid.L4c53:
__sbr_cell_28_588:
    mov eax, ecx
__sbr_cell_28_588_end:
__sbr_cell_28_589:
    lea rcx, [rip+ceil_log2]
__sbr_cell_28_589_end:
read_sbr_grid.L4c5c:
__sbr_cell_28_590:
    movsx eax, BYTE PTR [rax+rcx*1+0]
__sbr_cell_28_590_end:
__sbr_cell_28_591:
    mov esi, DWORD PTR [rdx+8]
__sbr_cell_28_591_end:
__sbr_cell_28_592:
    mov r9d, DWORD PTR [rdx+16]
__sbr_cell_28_592_end:
__sbr_cell_28_593:
    mov r8d, esi
__sbr_cell_28_593_end:
__sbr_cell_28_594:
    mov ecx, esi
__sbr_cell_28_594_end:
__sbr_cell_28_595:
    add esi, eax
__sbr_cell_28_595_end:
__sbr_cell_28_596:
    neg al
__sbr_cell_28_596_end:
__sbr_cell_28_597:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_597_end:
__sbr_cell_28_598:
    shr r8d, 3
__sbr_cell_28_598_end:
__sbr_cell_28_599:
    mov r8d, DWORD PTR [r10+r8*1+0]
__sbr_cell_28_599_end:
__sbr_cell_28_600:
    bswap r8d
__sbr_cell_28_600_end:
__sbr_cell_28_601:
    and cl, 7
__sbr_cell_28_601_end:
__sbr_cell_28_602:
    shl r8d, cl
__sbr_cell_28_602_end:
__sbr_cell_28_603:
    mov ecx, eax
__sbr_cell_28_603_end:
__sbr_cell_28_604:
    shr r8d, cl
__sbr_cell_28_604_end:
__sbr_cell_28_605:
    cmp r9d, esi
__sbr_cell_28_605_end:
__sbr_cell_28_606:
    cmovb esi, r9d
__sbr_cell_28_606_end:
__sbr_cell_28_607:
    mov DWORD PTR [rdx+8], esi
__sbr_cell_28_607_end:
read_sbr_grid.L4c93:
__sbr_cell_28_608:
    movsxd rsi, DWORD PTR [rbx+8]
__sbr_cell_28_608_end:
__sbr_cell_28_609:
    test rsi, rsi
__sbr_cell_28_609_end:
__sbr_cell_28_610:
    jle read_sbr_grid.L4ea2
__sbr_cell_28_610_end:
__sbr_cell_28_611:
    cmp esi, 1
__sbr_cell_28_611_end:
__sbr_cell_28_612:
    jne read_sbr_grid.L4df1
__sbr_cell_28_612_end:
read_sbr_grid.L4ca9:
__sbr_cell_28_613:
    xor eax, eax
__sbr_cell_28_613_end:
__sbr_cell_28_614:
    jmp read_sbr_grid.L4e73
__sbr_cell_28_614_end:
read_sbr_grid.L4cb0:
__sbr_cell_28_615:
    mov DWORD PTR [rbx+8], r8d
__sbr_cell_28_615_end:
__sbr_cell_28_616:
    test eax, eax
__sbr_cell_28_616_end:
__sbr_cell_28_617:
    je read_sbr_grid.L4cc9
__sbr_cell_28_617_end:
__sbr_cell_28_618:
    mov BYTE PTR [rbx+88732], 0
__sbr_cell_28_618_end:
__sbr_cell_28_619:
    cmp eax, 4
__sbr_cell_28_619_end:
__sbr_cell_28_620:
    jb read_sbr_grid.L4cd7
__sbr_cell_28_620_end:
__sbr_cell_28_621:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_621_end:
read_sbr_grid.L4cc9:
__sbr_cell_28_622:
    mov DWORD PTR [rbx+100], 0
__sbr_cell_28_622_end:
__sbr_cell_28_623:
    mov BYTE PTR [rbx+88732], 0
__sbr_cell_28_623_end:
read_sbr_grid.L4cd7:
__sbr_cell_28_624:
    lea r9d, [r8-1]
__sbr_cell_28_624_end:
__sbr_cell_28_625:
    mov BYTE PTR [rbx+r8*1+88732], 16
__sbr_cell_28_625_end:
__sbr_cell_28_626:
    mov esi, r8d
__sbr_cell_28_626_end:
__sbr_cell_28_627:
    shr esi, 1
__sbr_cell_28_627_end:
__sbr_cell_28_628:
    add sil, 16
__sbr_cell_28_628_end:
__sbr_cell_28_629:
    mov ecx, eax
__sbr_cell_28_629_end:
__sbr_cell_28_630:
    shr sil, cl
__sbr_cell_28_630_end:
__sbr_cell_28_631:
    test r9d, r9d
__sbr_cell_28_631_end:
__sbr_cell_28_632:
    je read_sbr_grid.L4d8b
__sbr_cell_28_632_end:
read_sbr_grid.L4cfb:
__sbr_cell_28_633:
    lea eax, [r8-10]
__sbr_cell_28_633_end:
__sbr_cell_28_634:
    cmp eax, 4294967288
__sbr_cell_28_634_end:
__sbr_cell_28_635:
    jb read_sbr_grid.L5131
__sbr_cell_28_635_end:
read_sbr_grid.L4d08:
__sbr_cell_28_636:
    mov BYTE PTR [rbx+88733], sil
__sbr_cell_28_636_end:
__sbr_cell_28_637:
    cmp r9d, 1
__sbr_cell_28_637_end:
__sbr_cell_28_638:
    je read_sbr_grid.L4d8b
__sbr_cell_28_638_end:
read_sbr_grid.L4d15:
__sbr_cell_28_639:
    lea eax, [rsi+rsi*1+0]
__sbr_cell_28_639_end:
__sbr_cell_28_640:
    mov BYTE PTR [rbx+88734], al
__sbr_cell_28_640_end:
__sbr_cell_28_641:
    cmp r9d, 2
__sbr_cell_28_641_end:
__sbr_cell_28_642:
    je read_sbr_grid.L4d8b
__sbr_cell_28_642_end:
read_sbr_grid.L4d24:
__sbr_cell_28_643:
    movzx eax, sil
__sbr_cell_28_643_end:
__sbr_cell_28_644:
    lea ecx, [rax+rax*2+0]
__sbr_cell_28_644_end:
__sbr_cell_28_645:
    mov BYTE PTR [rbx+88735], cl
__sbr_cell_28_645_end:
__sbr_cell_28_646:
    cmp r9d, 3
__sbr_cell_28_646_end:
__sbr_cell_28_647:
    je read_sbr_grid.L4d8b
__sbr_cell_28_647_end:
read_sbr_grid.L4d37:
__sbr_cell_28_648:
    lea ecx, [rsi*4+0]
__sbr_cell_28_648_end:
__sbr_cell_28_649:
    mov BYTE PTR [rbx+88736], cl
__sbr_cell_28_649_end:
__sbr_cell_28_650:
    cmp r9d, 4
__sbr_cell_28_650_end:
__sbr_cell_28_651:
    je read_sbr_grid.L4d8b
__sbr_cell_28_651_end:
read_sbr_grid.L4d4a:
__sbr_cell_28_652:
    lea ecx, [rax+rax*4+0]
__sbr_cell_28_652_end:
__sbr_cell_28_653:
    mov BYTE PTR [rbx+88737], cl
__sbr_cell_28_653_end:
__sbr_cell_28_654:
    cmp r9d, 5
__sbr_cell_28_654_end:
__sbr_cell_28_655:
    je read_sbr_grid.L4d8b
__sbr_cell_28_655_end:
read_sbr_grid.L4d59:
__sbr_cell_28_656:
    lea ecx, [rax+rax*1+0]
__sbr_cell_28_656_end:
__sbr_cell_28_657:
    lea ecx, [rcx+rcx*2+0]
__sbr_cell_28_657_end:
__sbr_cell_28_658:
    mov BYTE PTR [rbx+88738], cl
__sbr_cell_28_658_end:
__sbr_cell_28_659:
    cmp r9d, 6
__sbr_cell_28_659_end:
__sbr_cell_28_660:
    je read_sbr_grid.L4d8b
__sbr_cell_28_660_end:
read_sbr_grid.L4d6b:
__sbr_cell_28_661:
    lea ecx, [rax*8+0]
__sbr_cell_28_661_end:
__sbr_cell_28_662:
    sub ecx, eax
__sbr_cell_28_662_end:
__sbr_cell_28_663:
    mov BYTE PTR [rbx+88739], cl
__sbr_cell_28_663_end:
__sbr_cell_28_664:
    cmp r9d, 7
__sbr_cell_28_664_end:
__sbr_cell_28_665:
    je read_sbr_grid.L4d8b
__sbr_cell_28_665_end:
read_sbr_grid.L4d80:
__sbr_cell_28_666:
    shl sil, 3
__sbr_cell_28_666_end:
__sbr_cell_28_667:
    mov BYTE PTR [rbx+88740], sil
__sbr_cell_28_667_end:
read_sbr_grid.L4d8b:
__sbr_cell_28_668:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_668_end:
__sbr_cell_28_669:
    mov rax, QWORD PTR [rdx+0]
__sbr_cell_28_669_end:
__sbr_cell_28_670:
    mov esi, ecx
__sbr_cell_28_670_end:
__sbr_cell_28_671:
    shr esi, 3
__sbr_cell_28_671_end:
__sbr_cell_28_672:
    xor r8d, r8d
__sbr_cell_28_672_end:
__sbr_cell_28_673:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_673_end:
__sbr_cell_28_674:
    setl r8b
__sbr_cell_28_674_end:
__sbr_cell_28_675:
    add r8d, ecx
__sbr_cell_28_675_end:
__sbr_cell_28_676:
    movzx eax, BYTE PTR [rax+rsi*1+0]
__sbr_cell_28_676_end:
__sbr_cell_28_677:
    and cl, 7
__sbr_cell_28_677_end:
__sbr_cell_28_678:
    shl eax, cl
__sbr_cell_28_678_end:
__sbr_cell_28_679:
    mov DWORD PTR [rdx+8], r8d
__sbr_cell_28_679_end:
__sbr_cell_28_680:
    shr al, 7
__sbr_cell_28_680_end:
__sbr_cell_28_681:
    mov BYTE PTR [rbx+13], al
__sbr_cell_28_681_end:
read_sbr_grid.L4db6:
__sbr_cell_28_682:
    mov edx, DWORD PTR [rbx+8]
__sbr_cell_28_682_end:
__sbr_cell_28_683:
    cmp rdx, 2
__sbr_cell_28_683_end:
__sbr_cell_28_684:
    jb read_sbr_grid.L4de0
__sbr_cell_28_684_end:
read_sbr_grid.L4dbf:
__sbr_cell_28_685:
    lea ecx, [rdx-9]
__sbr_cell_28_685_end:
__sbr_cell_28_686:
    cmp ecx, 4294967289
__sbr_cell_28_686_end:
__sbr_cell_28_687:
    jb read_sbr_grid.L5136
__sbr_cell_28_687_end:
read_sbr_grid.L4dcb:
__sbr_cell_28_688:
    mov r12, rdi
__sbr_cell_28_688_end:
__sbr_cell_28_689:
    lea rdi, [rbx+14]
__sbr_cell_28_689_end:
__sbr_cell_28_690:
    dec rdx
__sbr_cell_28_690_end:
__sbr_cell_28_691:
    movzx esi, al
__sbr_cell_28_691_end:
__sbr_cell_28_692:
    call memset
__sbr_cell_28_692_end:
read_sbr_grid.L4ddd:
__sbr_cell_28_693:
    mov rdi, r12
__sbr_cell_28_693_end:
read_sbr_grid.L4de0:
__sbr_cell_28_694:
    mov DWORD PTR [rbx+0], r15d
__sbr_cell_28_694_end:
__sbr_cell_28_695:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_28_695_end:
__sbr_cell_28_696:
    lea eax, [rcx+1]
__sbr_cell_28_696_end:
__sbr_cell_28_697:
    xor r8d, r8d
__sbr_cell_28_697_end:
__sbr_cell_28_698:
    jmp read_sbr_grid.L4ed8
__sbr_cell_28_698_end:
read_sbr_grid.L4df1:
__sbr_cell_28_699:
    mov r9d, esi
__sbr_cell_28_699_end:
__sbr_cell_28_700:
    and r9d, 2147483646
__sbr_cell_28_700_end:
__sbr_cell_28_701:
    xor eax, eax
__sbr_cell_28_701_end:
__sbr_cell_28_702:
    .nops 1
__sbr_cell_28_702_end:
read_sbr_grid.L4e00:
__sbr_cell_28_703:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_703_end:
__sbr_cell_28_704:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_704_end:
__sbr_cell_28_705:
    mov r11d, ecx
__sbr_cell_28_705_end:
__sbr_cell_28_706:
    shr r11d, 3
__sbr_cell_28_706_end:
__sbr_cell_28_707:
    xor r12d, r12d
__sbr_cell_28_707_end:
__sbr_cell_28_708:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_708_end:
__sbr_cell_28_709:
    setl r12b
__sbr_cell_28_709_end:
__sbr_cell_28_710:
    add r12d, ecx
__sbr_cell_28_710_end:
__sbr_cell_28_711:
    movzx r10d, BYTE PTR [r10+r11*1+0]
__sbr_cell_28_711_end:
__sbr_cell_28_712:
    and cl, 7
__sbr_cell_28_712_end:
__sbr_cell_28_713:
    shl r10d, cl
__sbr_cell_28_713_end:
__sbr_cell_28_714:
    mov DWORD PTR [rdx+8], r12d
__sbr_cell_28_714_end:
__sbr_cell_28_715:
    shr r10b, 7
__sbr_cell_28_715_end:
__sbr_cell_28_716:
    mov BYTE PTR [rbx+rax*1+13], r10b
__sbr_cell_28_716_end:
read_sbr_grid.L4e32:
__sbr_cell_28_717:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_717_end:
__sbr_cell_28_718:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_718_end:
__sbr_cell_28_719:
    mov r11d, ecx
__sbr_cell_28_719_end:
__sbr_cell_28_720:
    shr r11d, 3
__sbr_cell_28_720_end:
__sbr_cell_28_721:
    xor r12d, r12d
__sbr_cell_28_721_end:
__sbr_cell_28_722:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_722_end:
__sbr_cell_28_723:
    setl r12b
__sbr_cell_28_723_end:
__sbr_cell_28_724:
    add r12d, ecx
__sbr_cell_28_724_end:
__sbr_cell_28_725:
    movzx r10d, BYTE PTR [r10+r11*1+0]
__sbr_cell_28_725_end:
__sbr_cell_28_726:
    and cl, 7
__sbr_cell_28_726_end:
__sbr_cell_28_727:
    shl r10d, cl
__sbr_cell_28_727_end:
__sbr_cell_28_728:
    mov DWORD PTR [rdx+8], r12d
__sbr_cell_28_728_end:
__sbr_cell_28_729:
    shr r10b, 7
__sbr_cell_28_729_end:
__sbr_cell_28_730:
    mov BYTE PTR [rbx+rax*1+14], r10b
__sbr_cell_28_730_end:
read_sbr_grid.L4e64:
__sbr_cell_28_731:
    add rax, 2
__sbr_cell_28_731_end:
__sbr_cell_28_732:
    cmp r9, rax
__sbr_cell_28_732_end:
__sbr_cell_28_733:
    jne read_sbr_grid.L4e00
__sbr_cell_28_733_end:
read_sbr_grid.L4e6d:
__sbr_cell_28_734:
    test sil, 1
__sbr_cell_28_734_end:
__sbr_cell_28_735:
    je read_sbr_grid.L4ea2
__sbr_cell_28_735_end:
read_sbr_grid.L4e73:
__sbr_cell_28_736:
    mov ecx, DWORD PTR [rdx+8]
__sbr_cell_28_736_end:
__sbr_cell_28_737:
    mov esi, ecx
__sbr_cell_28_737_end:
__sbr_cell_28_738:
    shr esi, 3
__sbr_cell_28_738_end:
__sbr_cell_28_739:
    xor r9d, r9d
__sbr_cell_28_739_end:
__sbr_cell_28_740:
    cmp ecx, DWORD PTR [rdx+16]
__sbr_cell_28_740_end:
__sbr_cell_28_741:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_28_741_end:
__sbr_cell_28_742:
    setl r9b
__sbr_cell_28_742_end:
__sbr_cell_28_743:
    add r9d, ecx
__sbr_cell_28_743_end:
__sbr_cell_28_744:
    movzx esi, BYTE PTR [r10+rsi*1+0]
__sbr_cell_28_744_end:
__sbr_cell_28_745:
    and cl, 7
__sbr_cell_28_745_end:
__sbr_cell_28_746:
    shl esi, cl
__sbr_cell_28_746_end:
__sbr_cell_28_747:
    mov DWORD PTR [rdx+8], r9d
__sbr_cell_28_747_end:
__sbr_cell_28_748:
    shr sil, 7
__sbr_cell_28_748_end:
__sbr_cell_28_749:
    mov BYTE PTR [rbx+rax*1+13], sil
__sbr_cell_28_749_end:
read_sbr_grid.L4ea2:
__sbr_cell_28_750:
    mov DWORD PTR [rbx+0], r15d
__sbr_cell_28_750_end:
__sbr_cell_28_751:
    test r8d, r8d
__sbr_cell_28_751_end:
__sbr_cell_28_752:
    js read_sbr_grid.L50e8
__sbr_cell_28_752_end:
__sbr_cell_28_753:
    mov ecx, DWORD PTR [rbx+8]
__sbr_cell_28_753_end:
__sbr_cell_28_754:
    lea eax, [rcx+1]
__sbr_cell_28_754_end:
__sbr_cell_28_755:
    cmp r8d, eax
__sbr_cell_28_755_end:
__sbr_cell_28_756:
    jbe read_sbr_grid.L4ed8
__sbr_cell_28_756_end:
__sbr_cell_28_757:
    mov rdi, QWORD PTR [rdi+8]
__sbr_cell_28_757_end:
__sbr_cell_28_758:
    lea rdx, [rip+L_str_28]
__sbr_cell_28_758_end:
read_sbr_grid.L4ec4:
__sbr_cell_28_759:
    mov esi, 16
__sbr_cell_28_759_end:
__sbr_cell_28_760:
    mov ecx, r8d
__sbr_cell_28_760_end:
read_sbr_grid.L4ecc:
__sbr_cell_28_761:
    xor eax, eax
__sbr_cell_28_761_end:
__sbr_cell_28_762:
    call av_log
__sbr_cell_28_762_end:
read_sbr_grid.L4ed3:
__sbr_cell_28_763:
    jmp read_sbr_grid.L5086
__sbr_cell_28_763_end:
read_sbr_grid.L4ed8:
__sbr_cell_28_764:
    test ecx, ecx
__sbr_cell_28_764_end:
__sbr_cell_28_765:
    je read_sbr_grid.L4f51
__sbr_cell_28_765_end:
__sbr_cell_28_766:
    movzx edx, BYTE PTR [rbx+88732]
__sbr_cell_28_766_end:
__sbr_cell_28_767:
    movzx esi, BYTE PTR [rbx+88733]
__sbr_cell_28_767_end:
__sbr_cell_28_768:
    cmp dl, sil
__sbr_cell_28_768_end:
__sbr_cell_28_769:
    jae read_sbr_grid.L506f
__sbr_cell_28_769_end:
__sbr_cell_28_770:
    cmp eax, 2
__sbr_cell_28_770_end:
__sbr_cell_28_771:
    jne read_sbr_grid.L4fd3
__sbr_cell_28_771_end:
read_sbr_grid.L4efc:
__sbr_cell_28_772:
    xor esi, esi
__sbr_cell_28_772_end:
__sbr_cell_28_773:
    cmp ecx, 1
__sbr_cell_28_773_end:
__sbr_cell_28_774:
    setne sil
__sbr_cell_28_774_end:
__sbr_cell_28_775:
    lea edi, [rsi+1]
__sbr_cell_28_775_end:
__sbr_cell_28_776:
    mov DWORD PTR [rbx+24], edi
__sbr_cell_28_776_end:
__sbr_cell_28_777:
    mov BYTE PTR [rbx+88742], dl
__sbr_cell_28_777_end:
read_sbr_grid.L4f11:
__sbr_cell_28_778:
    mov edx, ecx
__sbr_cell_28_778_end:
__sbr_cell_28_779:
    movzx edx, BYTE PTR [rbx+rdx*1+88732]
__sbr_cell_28_779_end:
__sbr_cell_28_780:
    mov BYTE PTR [rsi+rbx*1+88743], dl
__sbr_cell_28_780_end:
read_sbr_grid.L4f22:
__sbr_cell_28_781:
    cmp ecx, 1
__sbr_cell_28_781_end:
__sbr_cell_28_782:
    je read_sbr_grid.L4f75
__sbr_cell_28_782_end:
read_sbr_grid.L4f27:
__sbr_cell_28_783:
    test r15d, r15d
__sbr_cell_28_783_end:
__sbr_cell_28_784:
    je read_sbr_grid.L5094
__sbr_cell_28_784_end:
__sbr_cell_28_785:
    test r15b, 1
__sbr_cell_28_785_end:
__sbr_cell_28_786:
    jne read_sbr_grid.L509b
__sbr_cell_28_786_end:
__sbr_cell_28_787:
    test r8d, r8d
__sbr_cell_28_787_end:
__sbr_cell_28_788:
    je read_sbr_grid.L50ae
__sbr_cell_28_788_end:
__sbr_cell_28_789:
    cmp r8d, 1
__sbr_cell_28_789_end:
__sbr_cell_28_790:
    jne read_sbr_grid.L50b8
__sbr_cell_28_790_end:
__sbr_cell_28_791:
    dec ecx
__sbr_cell_28_791_end:
__sbr_cell_28_792:
    jmp read_sbr_grid.L4f65
__sbr_cell_28_792_end:
read_sbr_grid.L4f51:
__sbr_cell_28_793:
    movzx edx, BYTE PTR [rbx+88732]
__sbr_cell_28_793_end:
__sbr_cell_28_794:
    mov DWORD PTR [rbx+24], 1
__sbr_cell_28_794_end:
__sbr_cell_28_795:
    mov BYTE PTR [rbx+88742], dl
__sbr_cell_28_795_end:
read_sbr_grid.L4f65:
__sbr_cell_28_796:
    mov ecx, ecx
__sbr_cell_28_796_end:
__sbr_cell_28_797:
    movzx ecx, BYTE PTR [rbx+rcx*1+88732]
__sbr_cell_28_797_end:
__sbr_cell_28_798:
    mov BYTE PTR [rbx+88743], cl
__sbr_cell_28_798_end:
read_sbr_grid.L4f75:
__sbr_cell_28_799:
    xor ecx, ecx
__sbr_cell_28_799_end:
__sbr_cell_28_800:
    cmp DWORD PTR [rbx+14600], r14d
__sbr_cell_28_800_end:
__sbr_cell_28_801:
    setne cl
__sbr_cell_28_801_end:
__sbr_cell_28_802:
    neg ecx
__sbr_cell_28_802_end:
__sbr_cell_28_803:
    mov DWORD PTR [rbx+14596], ecx
__sbr_cell_28_803_end:
__sbr_cell_28_804:
    mov DWORD PTR [rbx+14600], 4294967295
__sbr_cell_28_804_end:
read_sbr_grid.L4f93:
__sbr_cell_28_805:
    test r8d, r8d
__sbr_cell_28_805_end:
__sbr_cell_28_806:
    je read_sbr_grid.L4fae
__sbr_cell_28_806_end:
__sbr_cell_28_807:
    test r15b, 1
__sbr_cell_28_807_end:
__sbr_cell_28_808:
    je read_sbr_grid.L4fae
__sbr_cell_28_808_end:
__sbr_cell_28_809:
    sub eax, r8d
__sbr_cell_28_809_end:
__sbr_cell_28_810:
    mov DWORD PTR [rbx+14600], eax
__sbr_cell_28_810_end:
__sbr_cell_28_811:
    xor eax, eax
__sbr_cell_28_811_end:
__sbr_cell_28_812:
    jmp read_sbr_grid.L508b
__sbr_cell_28_812_end:
read_sbr_grid.L4fae:
__sbr_cell_28_813:
    xor eax, eax
__sbr_cell_28_813_end:
__sbr_cell_28_814:
    cmp r15d, 2
__sbr_cell_28_814_end:
__sbr_cell_28_815:
    jne read_sbr_grid.L508b
__sbr_cell_28_815_end:
__sbr_cell_28_816:
    cmp r8d, 2
__sbr_cell_28_816_end:
__sbr_cell_28_817:
    jb read_sbr_grid.L508b
__sbr_cell_28_817_end:
__sbr_cell_28_818:
    dec r8d
__sbr_cell_28_818_end:
__sbr_cell_28_819:
    mov DWORD PTR [rbx+14600], r8d
__sbr_cell_28_819_end:
__sbr_cell_28_820:
    jmp read_sbr_grid.L508b
__sbr_cell_28_820_end:
read_sbr_grid.L4fd3:
__sbr_cell_28_821:
    movzx r9d, BYTE PTR [rbx+88734]
__sbr_cell_28_821_end:
__sbr_cell_28_822:
    cmp sil, r9b
__sbr_cell_28_822_end:
__sbr_cell_28_823:
    jae read_sbr_grid.L506f
__sbr_cell_28_823_end:
__sbr_cell_28_824:
    cmp eax, 3
__sbr_cell_28_824_end:
__sbr_cell_28_825:
    je read_sbr_grid.L4efc
__sbr_cell_28_825_end:
read_sbr_grid.L4fed:
__sbr_cell_28_826:
    movzx esi, BYTE PTR [rbx+88735]
__sbr_cell_28_826_end:
__sbr_cell_28_827:
    cmp r9b, sil
__sbr_cell_28_827_end:
__sbr_cell_28_828:
    jae read_sbr_grid.L506f
__sbr_cell_28_828_end:
__sbr_cell_28_829:
    cmp eax, 4
__sbr_cell_28_829_end:
__sbr_cell_28_830:
    je read_sbr_grid.L4efc
__sbr_cell_28_830_end:
read_sbr_grid.L5002:
__sbr_cell_28_831:
    movzx r9d, BYTE PTR [rbx+88736]
__sbr_cell_28_831_end:
__sbr_cell_28_832:
    cmp sil, r9b
__sbr_cell_28_832_end:
__sbr_cell_28_833:
    jae read_sbr_grid.L506f
__sbr_cell_28_833_end:
__sbr_cell_28_834:
    cmp eax, 5
__sbr_cell_28_834_end:
__sbr_cell_28_835:
    je read_sbr_grid.L4efc
__sbr_cell_28_835_end:
read_sbr_grid.L5018:
__sbr_cell_28_836:
    movzx esi, BYTE PTR [rbx+88737]
__sbr_cell_28_836_end:
__sbr_cell_28_837:
    cmp r9b, sil
__sbr_cell_28_837_end:
__sbr_cell_28_838:
    jae read_sbr_grid.L506f
__sbr_cell_28_838_end:
__sbr_cell_28_839:
    cmp eax, 6
__sbr_cell_28_839_end:
__sbr_cell_28_840:
    je read_sbr_grid.L4efc
__sbr_cell_28_840_end:
read_sbr_grid.L502d:
__sbr_cell_28_841:
    movzx r9d, BYTE PTR [rbx+88738]
__sbr_cell_28_841_end:
__sbr_cell_28_842:
    cmp sil, r9b
__sbr_cell_28_842_end:
__sbr_cell_28_843:
    jae read_sbr_grid.L506f
__sbr_cell_28_843_end:
__sbr_cell_28_844:
    cmp eax, 7
__sbr_cell_28_844_end:
__sbr_cell_28_845:
    je read_sbr_grid.L4efc
__sbr_cell_28_845_end:
read_sbr_grid.L5043:
__sbr_cell_28_846:
    movzx esi, BYTE PTR [rbx+88739]
__sbr_cell_28_846_end:
__sbr_cell_28_847:
    cmp r9b, sil
__sbr_cell_28_847_end:
__sbr_cell_28_848:
    jae read_sbr_grid.L506f
__sbr_cell_28_848_end:
__sbr_cell_28_849:
    cmp eax, 8
__sbr_cell_28_849_end:
__sbr_cell_28_850:
    je read_sbr_grid.L4efc
__sbr_cell_28_850_end:
read_sbr_grid.L5058:
__sbr_cell_28_851:
    cmp sil, BYTE PTR [rbx+88740]
__sbr_cell_28_851_end:
__sbr_cell_28_852:
    jae read_sbr_grid.L506f
__sbr_cell_28_852_end:
__sbr_cell_28_853:
    cmp eax, 9
__sbr_cell_28_853_end:
__sbr_cell_28_854:
    je read_sbr_grid.L4efc
__sbr_cell_28_854_end:
read_sbr_grid.L506a:
__sbr_cell_28_855:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_855_end:
read_sbr_grid.L506f:
__sbr_cell_28_856:
    mov rdi, QWORD PTR [rdi+8]
__sbr_cell_28_856_end:
__sbr_cell_28_857:
    lea rdx, [rip+L_str_29]
__sbr_cell_28_857_end:
__sbr_cell_28_858:
    mov esi, 16
__sbr_cell_28_858_end:
__sbr_cell_28_859:
    xor eax, eax
__sbr_cell_28_859_end:
__sbr_cell_28_860:
    call av_log
__sbr_cell_28_860_end:
read_sbr_grid.L5086:
__sbr_cell_28_861:
    mov eax, 4294967295
__sbr_cell_28_861_end:
read_sbr_grid.L508b:
__sbr_cell_28_862:
    pop rbx
__sbr_cell_28_862_end:
__sbr_cell_28_863:
    pop r12
__sbr_cell_28_863_end:
__sbr_cell_28_864:
    pop r14
__sbr_cell_28_864_end:
__sbr_cell_28_865:
    pop r15
__sbr_cell_28_865_end:
__sbr_cell_28_866:
    pop rbp
__sbr_cell_28_866_end:
read_sbr_grid.done:
__sbr_cell_28_867:
    ret
__sbr_cell_28_867_end:
read_sbr_grid.L5094:
__sbr_cell_28_868:
    shr ecx, 1
__sbr_cell_28_868_end:
__sbr_cell_28_869:
    jmp read_sbr_grid.L4f65
__sbr_cell_28_869_end:
read_sbr_grid.L509b:
__sbr_cell_28_870:
    cmp r8d, 3
__sbr_cell_28_870_end:
__sbr_cell_28_871:
    mov edx, 2
__sbr_cell_28_871_end:
__sbr_cell_28_872:
    cmovae edx, r8d
__sbr_cell_28_872_end:
__sbr_cell_28_873:
    sub ecx, edx
__sbr_cell_28_873_end:
__sbr_cell_28_874:
    inc ecx
__sbr_cell_28_874_end:
__sbr_cell_28_875:
    jmp read_sbr_grid.L50bc
__sbr_cell_28_875_end:
read_sbr_grid.L50ae:
__sbr_cell_28_876:
    mov ecx, 1
__sbr_cell_28_876_end:
__sbr_cell_28_877:
    jmp read_sbr_grid.L4f65
__sbr_cell_28_877_end:
read_sbr_grid.L50b8:
__sbr_cell_28_878:
    lea ecx, [r8-1]
__sbr_cell_28_878_end:
read_sbr_grid.L50bc:
__sbr_cell_28_879:
    cmp ecx, 9
__sbr_cell_28_879_end:
__sbr_cell_28_880:
    jb read_sbr_grid.L4f65
__sbr_cell_28_880_end:
__sbr_cell_28_881:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_881_end:
read_sbr_grid.L50ca:
__sbr_cell_28_882:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_882_end:
read_sbr_grid.L50cf:
__sbr_cell_28_883:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_883_end:
read_sbr_grid.L50d4:
__sbr_cell_28_884:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_884_end:
read_sbr_grid.L50d9:
__sbr_cell_28_885:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_885_end:
read_sbr_grid.L50de:
__sbr_cell_28_886:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_886_end:
read_sbr_grid.L50e3:
__sbr_cell_28_887:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_887_end:
read_sbr_grid.L50e8:
__sbr_cell_28_888:
    lea rdx, [rip+L_str_3]
__sbr_cell_28_888_end:
__sbr_cell_28_889:
    lea rcx, [rip+L_str_27]
__sbr_cell_28_889_end:
__sbr_cell_28_890:
    lea r8, [rip+L_str_5]
__sbr_cell_28_890_end:
__sbr_cell_28_891:
    xor edi, edi
__sbr_cell_28_891_end:
__sbr_cell_28_892:
    xor esi, esi
__sbr_cell_28_892_end:
__sbr_cell_28_893:
    mov r9d, 739
__sbr_cell_28_893_end:
__sbr_cell_28_894:
    xor eax, eax
__sbr_cell_28_894_end:
__sbr_cell_28_895:
    call av_log
__sbr_cell_28_895_end:
read_sbr_grid.L510e:
__sbr_cell_28_896:
    call abort
__sbr_cell_28_896_end:
read_sbr_grid.L5113:
__sbr_cell_28_897:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_897_end:
read_sbr_grid.L5118:
__sbr_cell_28_898:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_898_end:
read_sbr_grid.L511d:
__sbr_cell_28_899:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_899_end:
read_sbr_grid.L5122:
__sbr_cell_28_900:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_900_end:
read_sbr_grid.L5127:
__sbr_cell_28_901:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_901_end:
read_sbr_grid.L512c:
__sbr_cell_28_902:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_902_end:
read_sbr_grid.L5131:
__sbr_cell_28_903:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_903_end:
read_sbr_grid.L5136:
__sbr_cell_28_904:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_904_end:
read_sbr_grid.L513b:
__sbr_cell_28_905:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_28_905_end:
__sbr_cell_28_906:
    mov ecx, DWORD PTR [rdx+16]
__sbr_cell_28_906_end:
__sbr_cell_28_907:
    add eax, 2
__sbr_cell_28_907_end:
__sbr_cell_28_908:
    cmp ecx, eax
__sbr_cell_28_908_end:
__sbr_cell_28_909:
    cmovb eax, ecx
__sbr_cell_28_909_end:
__sbr_cell_28_910:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_28_910_end:
__sbr_cell_28_911:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_28_911_end:
__sbr_cell_28_912:
    int3
__sbr_cell_28_912_end:
__sbr_cell_28_913:
    int3
__sbr_cell_28_913_end:
__sbr_cell_28_914:
    int3
__sbr_cell_28_914_end:
__sbr_cell_28_915:
    int3
__sbr_cell_28_915_end:
__sbr_cell_28_916:
    int3
__sbr_cell_28_916_end:
__sbr_cell_28_917:
    int3
__sbr_cell_28_917_end:
__sbr_cell_28_918:
    int3
__sbr_cell_28_918_end:
__sbr_cell_28_919:
    int3
__sbr_cell_28_919_end:
__sbr_cell_28_920:
    int3
__sbr_cell_28_920_end:
__sbr_cell_28_921:
    int3
__sbr_cell_28_921_end:
__sbr_cell_28_922:
    int3
__sbr_cell_28_922_end:
__sbr_cell_28_923:
    int3
__sbr_cell_28_923_end:
__sbr_cell_28_924:
    int3
__sbr_cell_28_924_end:
__sbr_cell_28_925:
    int3
__sbr_cell_28_925_end:
__sbr_cell_28_926:
    int3
__sbr_cell_28_926_end:
.size read_sbr_grid, .-read_sbr_grid
.section .text.read_sbr_header,"ax",@progbits
.globl read_sbr_header
.type read_sbr_header,@function
read_sbr_header:
__sbr_cell_29_0:
    push rbp
__sbr_cell_29_0_end:
__sbr_cell_29_1:
    mov rbp, rsp
__sbr_cell_29_1_end:
__sbr_cell_29_2:
    push r14
__sbr_cell_29_2_end:
__sbr_cell_29_3:
    push rbx
__sbr_cell_29_3_end:
__sbr_cell_29_4:
    sub rsp, 16
__sbr_cell_29_4_end:
__sbr_cell_29_5:
    mov ebx, DWORD PTR [rsi+8]
__sbr_cell_29_5_end:
__sbr_cell_29_6:
    mov r8d, DWORD PTR [rdi+44]
__sbr_cell_29_6_end:
__sbr_cell_29_7:
    mov QWORD PTR [rdi+4], 1
__sbr_cell_29_7_end:
__sbr_cell_29_8:
    mov DWORD PTR [rdi+16], edx
__sbr_cell_29_8_end:
read_sbr_header.Ld1d:
__sbr_cell_29_9:
    movzx eax, WORD PTR [rdi+32]
__sbr_cell_29_9_end:
__sbr_cell_29_10:
    mov WORD PTR [rbp-20], ax
__sbr_cell_29_10_end:
__sbr_cell_29_11:
    mov eax, DWORD PTR [rdi+28]
__sbr_cell_29_11_end:
__sbr_cell_29_12:
    mov DWORD PTR [rbp-24], eax
__sbr_cell_29_12_end:
__sbr_cell_29_13:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_13_end:
__sbr_cell_29_14:
    test edx, edx
__sbr_cell_29_14_end:
__sbr_cell_29_15:
    je read_sbr_header.Ld91
__sbr_cell_29_15_end:
read_sbr_header.Ld32:
__sbr_cell_29_16:
    mov edx, DWORD PTR [rsi+16]
__sbr_cell_29_16_end:
__sbr_cell_29_17:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_17_end:
__sbr_cell_29_18:
    mov r9d, eax
__sbr_cell_29_18_end:
__sbr_cell_29_19:
    shr r9d, 3
__sbr_cell_29_19_end:
__sbr_cell_29_20:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_29_20_end:
__sbr_cell_29_21:
    bswap r9d
__sbr_cell_29_21_end:
__sbr_cell_29_22:
    mov ecx, eax
__sbr_cell_29_22_end:
__sbr_cell_29_23:
    and cl, 7
__sbr_cell_29_23_end:
__sbr_cell_29_24:
    shl r9d, cl
__sbr_cell_29_24_end:
__sbr_cell_29_25:
    shr r9d, 28
__sbr_cell_29_25_end:
__sbr_cell_29_26:
    add eax, 4
__sbr_cell_29_26_end:
__sbr_cell_29_27:
    cmp edx, eax
__sbr_cell_29_27_end:
__sbr_cell_29_28:
    cmovb eax, edx
__sbr_cell_29_28_end:
__sbr_cell_29_29:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_29_end:
__sbr_cell_29_30:
    mov BYTE PTR [rdi+28], r9b
__sbr_cell_29_30_end:
read_sbr_header.Ld61:
__sbr_cell_29_31:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_31_end:
__sbr_cell_29_32:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_32_end:
__sbr_cell_29_33:
    mov edx, eax
__sbr_cell_29_33_end:
__sbr_cell_29_34:
    shr edx, 3
__sbr_cell_29_34_end:
__sbr_cell_29_35:
    mov edx, DWORD PTR [rcx+rdx*1+0]
__sbr_cell_29_35_end:
__sbr_cell_29_36:
    bswap edx
__sbr_cell_29_36_end:
__sbr_cell_29_37:
    mov ecx, eax
__sbr_cell_29_37_end:
__sbr_cell_29_38:
    and cl, 7
__sbr_cell_29_38_end:
__sbr_cell_29_39:
    shl edx, cl
__sbr_cell_29_39_end:
__sbr_cell_29_40:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_29_40_end:
__sbr_cell_29_41:
    shr edx, 28
__sbr_cell_29_41_end:
__sbr_cell_29_42:
    add eax, 4
__sbr_cell_29_42_end:
__sbr_cell_29_43:
    cmp ecx, eax
__sbr_cell_29_43_end:
__sbr_cell_29_44:
    cmovb eax, ecx
__sbr_cell_29_44_end:
__sbr_cell_29_45:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_45_end:
__sbr_cell_29_46:
    mov BYTE PTR [rdi+29], dl
__sbr_cell_29_46_end:
__sbr_cell_29_47:
    jmp read_sbr_header.Le45
__sbr_cell_29_47_end:
read_sbr_header.Ld91:
__sbr_cell_29_48:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_48_end:
__sbr_cell_29_49:
    mov edx, eax
__sbr_cell_29_49_end:
__sbr_cell_29_50:
    shr edx, 3
__sbr_cell_29_50_end:
__sbr_cell_29_51:
    xor r9d, r9d
__sbr_cell_29_51_end:
__sbr_cell_29_52:
    cmp eax, DWORD PTR [rsi+16]
__sbr_cell_29_52_end:
__sbr_cell_29_53:
    setl r9b
__sbr_cell_29_53_end:
__sbr_cell_29_54:
    add r9d, eax
__sbr_cell_29_54_end:
__sbr_cell_29_55:
    movzx edx, BYTE PTR [rcx+rdx*1+0]
__sbr_cell_29_55_end:
__sbr_cell_29_56:
    and al, 7
__sbr_cell_29_56_end:
__sbr_cell_29_57:
    mov ecx, eax
__sbr_cell_29_57_end:
__sbr_cell_29_58:
    shl edx, cl
__sbr_cell_29_58_end:
__sbr_cell_29_59:
    shr edx, 7
__sbr_cell_29_59_end:
__sbr_cell_29_60:
    mov DWORD PTR [rsi+8], r9d
__sbr_cell_29_60_end:
__sbr_cell_29_61:
    and edx, 1
__sbr_cell_29_61_end:
__sbr_cell_29_62:
    mov DWORD PTR [rdi+36], edx
__sbr_cell_29_62_end:
read_sbr_header.Ldbd:
__sbr_cell_29_63:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_63_end:
__sbr_cell_29_64:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_64_end:
__sbr_cell_29_65:
    mov edx, eax
__sbr_cell_29_65_end:
__sbr_cell_29_66:
    shr edx, 3
__sbr_cell_29_66_end:
__sbr_cell_29_67:
    mov edx, DWORD PTR [rcx+rdx*1+0]
__sbr_cell_29_67_end:
__sbr_cell_29_68:
    bswap edx
__sbr_cell_29_68_end:
__sbr_cell_29_69:
    mov ecx, eax
__sbr_cell_29_69_end:
__sbr_cell_29_70:
    and cl, 7
__sbr_cell_29_70_end:
__sbr_cell_29_71:
    shl edx, cl
__sbr_cell_29_71_end:
__sbr_cell_29_72:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_29_72_end:
__sbr_cell_29_73:
    shr edx, 28
__sbr_cell_29_73_end:
__sbr_cell_29_74:
    add eax, 4
__sbr_cell_29_74_end:
__sbr_cell_29_75:
    cmp ecx, eax
__sbr_cell_29_75_end:
__sbr_cell_29_76:
    cmovb eax, ecx
__sbr_cell_29_76_end:
__sbr_cell_29_77:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_77_end:
__sbr_cell_29_78:
    mov BYTE PTR [rdi+28], dl
__sbr_cell_29_78_end:
read_sbr_header.Lde8:
__sbr_cell_29_79:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_79_end:
__sbr_cell_29_80:
    mov edx, DWORD PTR [rsi+16]
__sbr_cell_29_80_end:
__sbr_cell_29_81:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_81_end:
__sbr_cell_29_82:
    mov r9d, eax
__sbr_cell_29_82_end:
__sbr_cell_29_83:
    shr r9d, 3
__sbr_cell_29_83_end:
__sbr_cell_29_84:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_29_84_end:
__sbr_cell_29_85:
    bswap r9d
__sbr_cell_29_85_end:
__sbr_cell_29_86:
    mov ecx, eax
__sbr_cell_29_86_end:
__sbr_cell_29_87:
    and cl, 7
__sbr_cell_29_87_end:
__sbr_cell_29_88:
    shl r9d, cl
__sbr_cell_29_88_end:
__sbr_cell_29_89:
    shr r9d, 28
__sbr_cell_29_89_end:
__sbr_cell_29_90:
    add eax, 4
__sbr_cell_29_90_end:
__sbr_cell_29_91:
    cmp edx, eax
__sbr_cell_29_91_end:
__sbr_cell_29_92:
    cmovb eax, edx
__sbr_cell_29_92_end:
__sbr_cell_29_93:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_93_end:
__sbr_cell_29_94:
    mov BYTE PTR [rdi+29], r9b
__sbr_cell_29_94_end:
read_sbr_header.Le1a:
__sbr_cell_29_95:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_95_end:
__sbr_cell_29_96:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_96_end:
__sbr_cell_29_97:
    mov edx, eax
__sbr_cell_29_97_end:
__sbr_cell_29_98:
    shr edx, 3
__sbr_cell_29_98_end:
__sbr_cell_29_99:
    mov edx, DWORD PTR [rcx+rdx*1+0]
__sbr_cell_29_99_end:
__sbr_cell_29_100:
    bswap edx
__sbr_cell_29_100_end:
__sbr_cell_29_101:
    mov ecx, eax
__sbr_cell_29_101_end:
__sbr_cell_29_102:
    and cl, 7
__sbr_cell_29_102_end:
__sbr_cell_29_103:
    shl edx, cl
__sbr_cell_29_103_end:
__sbr_cell_29_104:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_29_104_end:
__sbr_cell_29_105:
    shr edx, 29
__sbr_cell_29_105_end:
__sbr_cell_29_106:
    add eax, 3
__sbr_cell_29_106_end:
__sbr_cell_29_107:
    cmp ecx, eax
__sbr_cell_29_107_end:
__sbr_cell_29_108:
    cmovb eax, ecx
__sbr_cell_29_108_end:
__sbr_cell_29_109:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_109_end:
__sbr_cell_29_110:
    mov BYTE PTR [rdi+30], dl
__sbr_cell_29_110_end:
read_sbr_header.Le45:
__sbr_cell_29_111:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_29_111_end:
__sbr_cell_29_112:
    mov r9d, DWORD PTR [rsi+16]
__sbr_cell_29_112_end:
__sbr_cell_29_113:
    add ecx, 2
__sbr_cell_29_113_end:
__sbr_cell_29_114:
    cmp r9d, ecx
__sbr_cell_29_114_end:
__sbr_cell_29_115:
    cmovb ecx, r9d
__sbr_cell_29_115_end:
__sbr_cell_29_116:
    mov DWORD PTR [rsi+8], ecx
__sbr_cell_29_116_end:
__sbr_cell_29_117:
    mov r10, QWORD PTR [rsi+0]
__sbr_cell_29_117_end:
__sbr_cell_29_118:
    mov edx, ecx
__sbr_cell_29_118_end:
__sbr_cell_29_119:
    shr edx, 3
__sbr_cell_29_119_end:
__sbr_cell_29_120:
    xor eax, eax
__sbr_cell_29_120_end:
__sbr_cell_29_121:
    cmp ecx, r9d
__sbr_cell_29_121_end:
__sbr_cell_29_122:
    setl al
__sbr_cell_29_122_end:
__sbr_cell_29_123:
    add eax, ecx
__sbr_cell_29_123_end:
__sbr_cell_29_124:
    movzx r14d, BYTE PTR [r10+rdx*1+0]
__sbr_cell_29_124_end:
__sbr_cell_29_125:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_125_end:
__sbr_cell_29_126:
    mov edx, eax
__sbr_cell_29_126_end:
__sbr_cell_29_127:
    shr edx, 3
__sbr_cell_29_127_end:
__sbr_cell_29_128:
    movzx edx, BYTE PTR [r10+rdx*1+0]
__sbr_cell_29_128_end:
__sbr_cell_29_129:
    xor r11d, r11d
__sbr_cell_29_129_end:
__sbr_cell_29_130:
    cmp eax, r9d
__sbr_cell_29_130_end:
__sbr_cell_29_131:
    setl r11b
__sbr_cell_29_131_end:
__sbr_cell_29_132:
    add r11d, eax
__sbr_cell_29_132_end:
__sbr_cell_29_133:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_29_133_end:
__sbr_cell_29_134:
    and cl, 7
__sbr_cell_29_134_end:
__sbr_cell_29_135:
    shl r14d, cl
__sbr_cell_29_135_end:
__sbr_cell_29_136:
    test r14b, r14b
__sbr_cell_29_136_end:
__sbr_cell_29_137:
    jns read_sbr_header.Lf31
__sbr_cell_29_137_end:
read_sbr_header.Le9d:
__sbr_cell_29_138:
    mov ecx, r11d
__sbr_cell_29_138_end:
__sbr_cell_29_139:
    shr ecx, 3
__sbr_cell_29_139_end:
__sbr_cell_29_140:
    mov r10d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_29_140_end:
__sbr_cell_29_141:
    bswap r10d
__sbr_cell_29_141_end:
__sbr_cell_29_142:
    mov ecx, r11d
__sbr_cell_29_142_end:
__sbr_cell_29_143:
    and cl, 7
__sbr_cell_29_143_end:
__sbr_cell_29_144:
    shl r10d, cl
__sbr_cell_29_144_end:
__sbr_cell_29_145:
    shr r10d, 30
__sbr_cell_29_145_end:
__sbr_cell_29_146:
    add r11d, 2
__sbr_cell_29_146_end:
__sbr_cell_29_147:
    cmp r9d, r11d
__sbr_cell_29_147_end:
__sbr_cell_29_148:
    cmovb r11d, r9d
__sbr_cell_29_148_end:
__sbr_cell_29_149:
    mov DWORD PTR [rsi+8], r11d
__sbr_cell_29_149_end:
__sbr_cell_29_150:
    mov BYTE PTR [rdi+31], r10b
__sbr_cell_29_150_end:
read_sbr_header.Leca:
__sbr_cell_29_151:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_29_151_end:
__sbr_cell_29_152:
    mov r9d, ecx
__sbr_cell_29_152_end:
__sbr_cell_29_153:
    shr r9d, 3
__sbr_cell_29_153_end:
__sbr_cell_29_154:
    xor r10d, r10d
__sbr_cell_29_154_end:
__sbr_cell_29_155:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_29_155_end:
__sbr_cell_29_156:
    mov r11, QWORD PTR [rsi+0]
__sbr_cell_29_156_end:
__sbr_cell_29_157:
    setl r10b
__sbr_cell_29_157_end:
__sbr_cell_29_158:
    add r10d, ecx
__sbr_cell_29_158_end:
__sbr_cell_29_159:
    movzx r9d, BYTE PTR [r11+r9*1+0]
__sbr_cell_29_159_end:
__sbr_cell_29_160:
    and cl, 7
__sbr_cell_29_160_end:
__sbr_cell_29_161:
    shl r9d, cl
__sbr_cell_29_161_end:
__sbr_cell_29_162:
    mov DWORD PTR [rsi+8], r10d
__sbr_cell_29_162_end:
__sbr_cell_29_163:
    shr r9b, 7
__sbr_cell_29_163_end:
__sbr_cell_29_164:
    mov BYTE PTR [rdi+32], r9b
__sbr_cell_29_164_end:
read_sbr_header.Lefb:
__sbr_cell_29_165:
    mov r10d, DWORD PTR [rsi+8]
__sbr_cell_29_165_end:
__sbr_cell_29_166:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_166_end:
__sbr_cell_29_167:
    mov r9d, r10d
__sbr_cell_29_167_end:
__sbr_cell_29_168:
    shr r9d, 3
__sbr_cell_29_168_end:
__sbr_cell_29_169:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_29_169_end:
__sbr_cell_29_170:
    bswap r9d
__sbr_cell_29_170_end:
__sbr_cell_29_171:
    mov ecx, r10d
__sbr_cell_29_171_end:
__sbr_cell_29_172:
    and cl, 7
__sbr_cell_29_172_end:
__sbr_cell_29_173:
    shl r9d, cl
__sbr_cell_29_173_end:
__sbr_cell_29_174:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_29_174_end:
__sbr_cell_29_175:
    shr r9d, 30
__sbr_cell_29_175_end:
__sbr_cell_29_176:
    add r10d, 2
__sbr_cell_29_176_end:
__sbr_cell_29_177:
    cmp ecx, r10d
__sbr_cell_29_177_end:
__sbr_cell_29_178:
    cmovb r10d, ecx
__sbr_cell_29_178_end:
__sbr_cell_29_179:
    mov DWORD PTR [rsi+8], r10d
__sbr_cell_29_179_end:
__sbr_cell_29_180:
    jmp read_sbr_header.Lf3a
__sbr_cell_29_180_end:
read_sbr_header.Lf31:
__sbr_cell_29_181:
    mov WORD PTR [rdi+31], 258
__sbr_cell_29_181_end:
__sbr_cell_29_182:
    mov r9b, 2
__sbr_cell_29_182_end:
read_sbr_header.Lf3a:
__sbr_cell_29_183:
    and eax, 7
__sbr_cell_29_183_end:
__sbr_cell_29_184:
    mov BYTE PTR [rdi+33], r9b
__sbr_cell_29_184_end:
__sbr_cell_29_185:
    mov ecx, DWORD PTR [rbp-24]
__sbr_cell_29_185_end:
__sbr_cell_29_186:
    xor ecx, DWORD PTR [rdi+28]
__sbr_cell_29_186_end:
__sbr_cell_29_187:
    movzx r9d, WORD PTR [rbp-20]
__sbr_cell_29_187_end:
__sbr_cell_29_188:
    xor r9w, WORD PTR [rdi+32]
__sbr_cell_29_188_end:
__sbr_cell_29_189:
    movzx r9d, r9w
__sbr_cell_29_189_end:
__sbr_cell_29_190:
    or r9d, ecx
__sbr_cell_29_190_end:
__sbr_cell_29_191:
    je read_sbr_header.Lf61
__sbr_cell_29_191_end:
__sbr_cell_29_192:
    mov DWORD PTR [rdi+24], 1
__sbr_cell_29_192_end:
read_sbr_header.Lf61:
__sbr_cell_29_193:
    mov ecx, eax
__sbr_cell_29_193_end:
__sbr_cell_29_194:
    shl edx, cl
__sbr_cell_29_194_end:
__sbr_cell_29_195:
    test dl, dl
__sbr_cell_29_195_end:
__sbr_cell_29_196:
    jns read_sbr_header.L102d
__sbr_cell_29_196_end:
read_sbr_header.Lf6d:
__sbr_cell_29_197:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_197_end:
__sbr_cell_29_198:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_198_end:
__sbr_cell_29_199:
    mov edx, eax
__sbr_cell_29_199_end:
__sbr_cell_29_200:
    shr edx, 3
__sbr_cell_29_200_end:
__sbr_cell_29_201:
    mov edx, DWORD PTR [rcx+rdx*1+0]
__sbr_cell_29_201_end:
__sbr_cell_29_202:
    bswap edx
__sbr_cell_29_202_end:
__sbr_cell_29_203:
    mov ecx, eax
__sbr_cell_29_203_end:
__sbr_cell_29_204:
    and cl, 7
__sbr_cell_29_204_end:
__sbr_cell_29_205:
    shl edx, cl
__sbr_cell_29_205_end:
__sbr_cell_29_206:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_29_206_end:
__sbr_cell_29_207:
    shr edx, 30
__sbr_cell_29_207_end:
__sbr_cell_29_208:
    add eax, 2
__sbr_cell_29_208_end:
__sbr_cell_29_209:
    cmp ecx, eax
__sbr_cell_29_209_end:
__sbr_cell_29_210:
    cmovb eax, ecx
__sbr_cell_29_210_end:
__sbr_cell_29_211:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_211_end:
__sbr_cell_29_212:
    mov DWORD PTR [rdi+44], edx
__sbr_cell_29_212_end:
read_sbr_header.Lf98:
__sbr_cell_29_213:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_213_end:
__sbr_cell_29_214:
    mov edx, DWORD PTR [rsi+16]
__sbr_cell_29_214_end:
__sbr_cell_29_215:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_29_215_end:
__sbr_cell_29_216:
    mov r9d, eax
__sbr_cell_29_216_end:
__sbr_cell_29_217:
    shr r9d, 3
__sbr_cell_29_217_end:
__sbr_cell_29_218:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_29_218_end:
__sbr_cell_29_219:
    bswap r9d
__sbr_cell_29_219_end:
__sbr_cell_29_220:
    mov ecx, eax
__sbr_cell_29_220_end:
__sbr_cell_29_221:
    and cl, 7
__sbr_cell_29_221_end:
__sbr_cell_29_222:
    shl r9d, cl
__sbr_cell_29_222_end:
__sbr_cell_29_223:
    shr r9d, 30
__sbr_cell_29_223_end:
__sbr_cell_29_224:
    add eax, 2
__sbr_cell_29_224_end:
__sbr_cell_29_225:
    cmp edx, eax
__sbr_cell_29_225_end:
__sbr_cell_29_226:
    cmovb eax, edx
__sbr_cell_29_226_end:
__sbr_cell_29_227:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_29_227_end:
__sbr_cell_29_228:
    mov DWORD PTR [rdi+48], r9d
__sbr_cell_29_228_end:
read_sbr_header.Lfca:
__sbr_cell_29_229:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_29_229_end:
__sbr_cell_29_230:
    mov rax, QWORD PTR [rsi+0]
__sbr_cell_29_230_end:
__sbr_cell_29_231:
    mov edx, ecx
__sbr_cell_29_231_end:
__sbr_cell_29_232:
    shr edx, 3
__sbr_cell_29_232_end:
__sbr_cell_29_233:
    xor r9d, r9d
__sbr_cell_29_233_end:
__sbr_cell_29_234:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_29_234_end:
__sbr_cell_29_235:
    setl r9b
__sbr_cell_29_235_end:
__sbr_cell_29_236:
    add r9d, ecx
__sbr_cell_29_236_end:
__sbr_cell_29_237:
    movzx eax, BYTE PTR [rax+rdx*1+0]
__sbr_cell_29_237_end:
__sbr_cell_29_238:
    and cl, 7
__sbr_cell_29_238_end:
__sbr_cell_29_239:
    shl eax, cl
__sbr_cell_29_239_end:
__sbr_cell_29_240:
    shr eax, 7
__sbr_cell_29_240_end:
__sbr_cell_29_241:
    mov DWORD PTR [rsi+8], r9d
__sbr_cell_29_241_end:
__sbr_cell_29_242:
    and eax, 1
__sbr_cell_29_242_end:
__sbr_cell_29_243:
    mov DWORD PTR [rdi+52], eax
__sbr_cell_29_243_end:
read_sbr_header.Lff8:
__sbr_cell_29_244:
    mov ecx, DWORD PTR [rsi+8]
__sbr_cell_29_244_end:
__sbr_cell_29_245:
    mov eax, ecx
__sbr_cell_29_245_end:
__sbr_cell_29_246:
    shr eax, 3
__sbr_cell_29_246_end:
__sbr_cell_29_247:
    xor edx, edx
__sbr_cell_29_247_end:
__sbr_cell_29_248:
    cmp ecx, DWORD PTR [rsi+16]
__sbr_cell_29_248_end:
__sbr_cell_29_249:
    mov r9, QWORD PTR [rsi+0]
__sbr_cell_29_249_end:
__sbr_cell_29_250:
    setl dl
__sbr_cell_29_250_end:
__sbr_cell_29_251:
    add edx, ecx
__sbr_cell_29_251_end:
__sbr_cell_29_252:
    movzx eax, BYTE PTR [r9+rax*1+0]
__sbr_cell_29_252_end:
__sbr_cell_29_253:
    and cl, 7
__sbr_cell_29_253_end:
__sbr_cell_29_254:
    shl eax, cl
__sbr_cell_29_254_end:
__sbr_cell_29_255:
    shr eax, 7
__sbr_cell_29_255_end:
__sbr_cell_29_256:
    mov DWORD PTR [rsi+8], edx
__sbr_cell_29_256_end:
__sbr_cell_29_257:
    and eax, 1
__sbr_cell_29_257_end:
__sbr_cell_29_258:
    mov ecx, DWORD PTR [rdi+44]
__sbr_cell_29_258_end:
__sbr_cell_29_259:
    mov DWORD PTR [rdi+56], eax
__sbr_cell_29_259_end:
__sbr_cell_29_260:
    cmp ecx, r8d
__sbr_cell_29_260_end:
__sbr_cell_29_261:
    jne read_sbr_header.L1054
__sbr_cell_29_261_end:
__sbr_cell_29_262:
    jmp read_sbr_header.L1065
__sbr_cell_29_262_end:
read_sbr_header.L102d:
__sbr_cell_29_263:
    mov rax, 8589934594
__sbr_cell_29_263_end:
__sbr_cell_29_264:
    mov QWORD PTR [rdi+44], rax
__sbr_cell_29_264_end:
__sbr_cell_29_265:
    mov DWORD PTR [rdi+52], 1
__sbr_cell_29_265_end:
__sbr_cell_29_266:
    mov eax, 1
__sbr_cell_29_266_end:
__sbr_cell_29_267:
    mov ecx, 2
__sbr_cell_29_267_end:
__sbr_cell_29_268:
    mov DWORD PTR [rdi+56], eax
__sbr_cell_29_268_end:
__sbr_cell_29_269:
    cmp ecx, r8d
__sbr_cell_29_269_end:
__sbr_cell_29_270:
    je read_sbr_header.L1065
__sbr_cell_29_270_end:
read_sbr_header.L1054:
__sbr_cell_29_271:
    cmp DWORD PTR [rdi+24], 0
__sbr_cell_29_271_end:
__sbr_cell_29_272:
    jne read_sbr_header.L1065
__sbr_cell_29_272_end:
read_sbr_header.L105a:
__sbr_cell_29_273:
    mov r14, rsi
__sbr_cell_29_273_end:
__sbr_cell_29_274:
    call sbr_make_f_tablelim
__sbr_cell_29_274_end:
read_sbr_header.L1062:
__sbr_cell_29_275:
    mov rsi, r14
__sbr_cell_29_275_end:
read_sbr_header.L1065:
__sbr_cell_29_276:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_29_276_end:
__sbr_cell_29_277:
    sub eax, ebx
__sbr_cell_29_277_end:
__sbr_cell_29_278:
    add rsp, 16
__sbr_cell_29_278_end:
__sbr_cell_29_279:
    pop rbx
__sbr_cell_29_279_end:
__sbr_cell_29_280:
    pop r14
__sbr_cell_29_280_end:
__sbr_cell_29_281:
    pop rbp
__sbr_cell_29_281_end:
read_sbr_header.done:
__sbr_cell_29_282:
    ret
__sbr_cell_29_282_end:
__sbr_cell_29_283:
    int3
__sbr_cell_29_283_end:
__sbr_cell_29_284:
    int3
__sbr_cell_29_284_end:
__sbr_cell_29_285:
    int3
__sbr_cell_29_285_end:
__sbr_cell_29_286:
    int3
__sbr_cell_29_286_end:
__sbr_cell_29_287:
    int3
__sbr_cell_29_287_end:
__sbr_cell_29_288:
    int3
__sbr_cell_29_288_end:
__sbr_cell_29_289:
    int3
__sbr_cell_29_289_end:
__sbr_cell_29_290:
    int3
__sbr_cell_29_290_end:
__sbr_cell_29_291:
    int3
__sbr_cell_29_291_end:
__sbr_cell_29_292:
    int3
__sbr_cell_29_292_end:
__sbr_cell_29_293:
    int3
__sbr_cell_29_293_end:
__sbr_cell_29_294:
    int3
__sbr_cell_29_294_end:
__sbr_cell_29_295:
    int3
__sbr_cell_29_295_end:
.size read_sbr_header, .-read_sbr_header
.section .text.read_sbr_invf,"ax",@progbits
.globl read_sbr_invf
.type read_sbr_invf,@function
read_sbr_invf:
__sbr_cell_30_0:
    movzx eax, BYTE PTR [rdx+43]
__sbr_cell_30_0_end:
__sbr_cell_30_1:
    mov BYTE PTR [rdx+48], al
__sbr_cell_30_1_end:
__sbr_cell_30_2:
    mov eax, DWORD PTR [rdx+39]
__sbr_cell_30_2_end:
__sbr_cell_30_3:
    mov DWORD PTR [rdx+44], eax
__sbr_cell_30_3_end:
__sbr_cell_30_4:
    cmp DWORD PTR [rdi+311784], 0
__sbr_cell_30_4_end:
__sbr_cell_30_5:
    je read_sbr_invf.L578f
__sbr_cell_30_5_end:
read_sbr_invf.L564a:
__sbr_cell_30_6:
    lea rax, [rdx+39]
__sbr_cell_30_6_end:
__sbr_cell_30_7:
    mov r8d, DWORD PTR [rsi+8]
__sbr_cell_30_7_end:
__sbr_cell_30_8:
    mov r9d, DWORD PTR [rsi+16]
__sbr_cell_30_8_end:
__sbr_cell_30_9:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_30_9_end:
__sbr_cell_30_10:
    mov r10d, r8d
__sbr_cell_30_10_end:
__sbr_cell_30_11:
    shr r10d, 3
__sbr_cell_30_11_end:
__sbr_cell_30_12:
    mov r10d, DWORD PTR [rcx+r10*1+0]
__sbr_cell_30_12_end:
__sbr_cell_30_13:
    bswap r10d
__sbr_cell_30_13_end:
__sbr_cell_30_14:
    mov ecx, r8d
__sbr_cell_30_14_end:
__sbr_cell_30_15:
    and cl, 7
__sbr_cell_30_15_end:
__sbr_cell_30_16:
    shl r10d, cl
__sbr_cell_30_16_end:
__sbr_cell_30_17:
    shr r10d, 30
__sbr_cell_30_17_end:
__sbr_cell_30_18:
    add r8d, 2
__sbr_cell_30_18_end:
__sbr_cell_30_19:
    cmp r9d, r8d
__sbr_cell_30_19_end:
__sbr_cell_30_20:
    cmovb r8d, r9d
__sbr_cell_30_20_end:
__sbr_cell_30_21:
    mov DWORD PTR [rsi+8], r8d
__sbr_cell_30_21_end:
__sbr_cell_30_22:
    mov BYTE PTR [rax+0], r10b
__sbr_cell_30_22_end:
__sbr_cell_30_23:
    cmp DWORD PTR [rdi+311784], 1
__sbr_cell_30_23_end:
__sbr_cell_30_24:
    jbe read_sbr_invf.L578f
__sbr_cell_30_24_end:
read_sbr_invf.L5693:
__sbr_cell_30_25:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_30_25_end:
__sbr_cell_30_26:
    mov r8d, DWORD PTR [rsi+16]
__sbr_cell_30_26_end:
__sbr_cell_30_27:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_30_27_end:
__sbr_cell_30_28:
    mov r9d, eax
__sbr_cell_30_28_end:
__sbr_cell_30_29:
    shr r9d, 3
__sbr_cell_30_29_end:
__sbr_cell_30_30:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_30_30_end:
__sbr_cell_30_31:
    bswap r9d
__sbr_cell_30_31_end:
__sbr_cell_30_32:
    mov ecx, eax
__sbr_cell_30_32_end:
__sbr_cell_30_33:
    and cl, 7
__sbr_cell_30_33_end:
__sbr_cell_30_34:
    shl r9d, cl
__sbr_cell_30_34_end:
__sbr_cell_30_35:
    shr r9d, 30
__sbr_cell_30_35_end:
__sbr_cell_30_36:
    add eax, 2
__sbr_cell_30_36_end:
__sbr_cell_30_37:
    cmp r8d, eax
__sbr_cell_30_37_end:
__sbr_cell_30_38:
    cmovb eax, r8d
__sbr_cell_30_38_end:
__sbr_cell_30_39:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_30_39_end:
__sbr_cell_30_40:
    mov BYTE PTR [rdx+40], r9b
__sbr_cell_30_40_end:
__sbr_cell_30_41:
    cmp DWORD PTR [rdi+311784], 3
__sbr_cell_30_41_end:
__sbr_cell_30_42:
    jb read_sbr_invf.L578f
__sbr_cell_30_42_end:
read_sbr_invf.L56d5:
__sbr_cell_30_43:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_30_43_end:
__sbr_cell_30_44:
    mov r8d, DWORD PTR [rsi+16]
__sbr_cell_30_44_end:
__sbr_cell_30_45:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_30_45_end:
__sbr_cell_30_46:
    mov r9d, eax
__sbr_cell_30_46_end:
__sbr_cell_30_47:
    shr r9d, 3
__sbr_cell_30_47_end:
__sbr_cell_30_48:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_30_48_end:
__sbr_cell_30_49:
    bswap r9d
__sbr_cell_30_49_end:
__sbr_cell_30_50:
    mov ecx, eax
__sbr_cell_30_50_end:
__sbr_cell_30_51:
    and cl, 7
__sbr_cell_30_51_end:
__sbr_cell_30_52:
    shl r9d, cl
__sbr_cell_30_52_end:
__sbr_cell_30_53:
    shr r9d, 30
__sbr_cell_30_53_end:
__sbr_cell_30_54:
    add eax, 2
__sbr_cell_30_54_end:
__sbr_cell_30_55:
    cmp r8d, eax
__sbr_cell_30_55_end:
__sbr_cell_30_56:
    cmovb eax, r8d
__sbr_cell_30_56_end:
__sbr_cell_30_57:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_30_57_end:
__sbr_cell_30_58:
    mov BYTE PTR [rdx+41], r9b
__sbr_cell_30_58_end:
__sbr_cell_30_59:
    cmp DWORD PTR [rdi+311784], 4
__sbr_cell_30_59_end:
__sbr_cell_30_60:
    jb read_sbr_invf.L578f
__sbr_cell_30_60_end:
read_sbr_invf.L5713:
__sbr_cell_30_61:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_30_61_end:
__sbr_cell_30_62:
    mov r8d, DWORD PTR [rsi+16]
__sbr_cell_30_62_end:
__sbr_cell_30_63:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_30_63_end:
__sbr_cell_30_64:
    mov r9d, eax
__sbr_cell_30_64_end:
__sbr_cell_30_65:
    shr r9d, 3
__sbr_cell_30_65_end:
__sbr_cell_30_66:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_30_66_end:
__sbr_cell_30_67:
    bswap r9d
__sbr_cell_30_67_end:
__sbr_cell_30_68:
    mov ecx, eax
__sbr_cell_30_68_end:
__sbr_cell_30_69:
    and cl, 7
__sbr_cell_30_69_end:
__sbr_cell_30_70:
    shl r9d, cl
__sbr_cell_30_70_end:
__sbr_cell_30_71:
    shr r9d, 30
__sbr_cell_30_71_end:
__sbr_cell_30_72:
    add eax, 2
__sbr_cell_30_72_end:
__sbr_cell_30_73:
    cmp r8d, eax
__sbr_cell_30_73_end:
__sbr_cell_30_74:
    cmovb eax, r8d
__sbr_cell_30_74_end:
__sbr_cell_30_75:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_30_75_end:
__sbr_cell_30_76:
    mov BYTE PTR [rdx+42], r9b
__sbr_cell_30_76_end:
__sbr_cell_30_77:
    cmp DWORD PTR [rdi+311784], 5
__sbr_cell_30_77_end:
__sbr_cell_30_78:
    jb read_sbr_invf.L578f
__sbr_cell_30_78_end:
read_sbr_invf.L5751:
__sbr_cell_30_79:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_30_79_end:
__sbr_cell_30_80:
    mov r8d, DWORD PTR [rsi+16]
__sbr_cell_30_80_end:
__sbr_cell_30_81:
    mov rcx, QWORD PTR [rsi+0]
__sbr_cell_30_81_end:
__sbr_cell_30_82:
    mov r9d, eax
__sbr_cell_30_82_end:
__sbr_cell_30_83:
    shr r9d, 3
__sbr_cell_30_83_end:
__sbr_cell_30_84:
    mov r9d, DWORD PTR [rcx+r9*1+0]
__sbr_cell_30_84_end:
__sbr_cell_30_85:
    bswap r9d
__sbr_cell_30_85_end:
__sbr_cell_30_86:
    mov ecx, eax
__sbr_cell_30_86_end:
__sbr_cell_30_87:
    and cl, 7
__sbr_cell_30_87_end:
__sbr_cell_30_88:
    shl r9d, cl
__sbr_cell_30_88_end:
__sbr_cell_30_89:
    shr r9d, 30
__sbr_cell_30_89_end:
__sbr_cell_30_90:
    add eax, 2
__sbr_cell_30_90_end:
__sbr_cell_30_91:
    cmp r8d, eax
__sbr_cell_30_91_end:
__sbr_cell_30_92:
    cmovb eax, r8d
__sbr_cell_30_92_end:
__sbr_cell_30_93:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_30_93_end:
__sbr_cell_30_94:
    mov BYTE PTR [rdx+43], r9b
__sbr_cell_30_94_end:
__sbr_cell_30_95:
    cmp DWORD PTR [rdi+311784], 5
__sbr_cell_30_95_end:
__sbr_cell_30_96:
    ja read_sbr_invf.L5790
__sbr_cell_30_96_end:
read_sbr_invf.L578f:
read_sbr_invf.done:
__sbr_cell_30_97:
    ret
__sbr_cell_30_97_end:
read_sbr_invf.L5790:
__sbr_cell_30_98:
    mov eax, DWORD PTR [rsi+8]
__sbr_cell_30_98_end:
__sbr_cell_30_99:
    mov ecx, DWORD PTR [rsi+16]
__sbr_cell_30_99_end:
__sbr_cell_30_100:
    add eax, 2
__sbr_cell_30_100_end:
__sbr_cell_30_101:
    cmp ecx, eax
__sbr_cell_30_101_end:
__sbr_cell_30_102:
    cmovb eax, ecx
__sbr_cell_30_102_end:
__sbr_cell_30_103:
    mov DWORD PTR [rsi+8], eax
__sbr_cell_30_103_end:
__sbr_cell_30_104:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_30_104_end:
__sbr_cell_30_105:
    int3
__sbr_cell_30_105_end:
__sbr_cell_30_106:
    int3
__sbr_cell_30_106_end:
__sbr_cell_30_107:
    int3
__sbr_cell_30_107_end:
__sbr_cell_30_108:
    int3
__sbr_cell_30_108_end:
__sbr_cell_30_109:
    int3
__sbr_cell_30_109_end:
__sbr_cell_30_110:
    int3
__sbr_cell_30_110_end:
__sbr_cell_30_111:
    int3
__sbr_cell_30_111_end:
__sbr_cell_30_112:
    int3
__sbr_cell_30_112_end:
__sbr_cell_30_113:
    int3
__sbr_cell_30_113_end:
__sbr_cell_30_114:
    int3
__sbr_cell_30_114_end:
.size read_sbr_invf, .-read_sbr_invf
.section .text.read_sbr_noise,"ax",@progbits
.globl read_sbr_noise
.type read_sbr_noise,@function
read_sbr_noise:
__sbr_cell_31_0:
    push rbp
__sbr_cell_31_0_end:
__sbr_cell_31_1:
    mov rbp, rsp
__sbr_cell_31_1_end:
__sbr_cell_31_2:
    push r15
__sbr_cell_31_2_end:
__sbr_cell_31_3:
    push r14
__sbr_cell_31_3_end:
__sbr_cell_31_4:
    push r13
__sbr_cell_31_4_end:
__sbr_cell_31_5:
    push r12
__sbr_cell_31_5_end:
__sbr_cell_31_6:
    push rbx
__sbr_cell_31_6_end:
__sbr_cell_31_7:
    sub rsp, 40
__sbr_cell_31_7_end:
read_sbr_noise.L6111:
__sbr_cell_31_8:
    mov r9, rcx
__sbr_cell_31_8_end:
__sbr_cell_31_9:
    test r8d, r8d
__sbr_cell_31_9_end:
__sbr_cell_31_10:
    setne cl
__sbr_cell_31_10_end:
__sbr_cell_31_11:
    mov eax, DWORD PTR [rsi+60]
__sbr_cell_31_11_end:
__sbr_cell_31_12:
    cmp eax, 1
__sbr_cell_31_12_end:
__sbr_cell_31_13:
    sete r11b
__sbr_cell_31_13_end:
__sbr_cell_31_14:
    test eax, eax
__sbr_cell_31_14_end:
__sbr_cell_31_15:
    setne r10b
__sbr_cell_31_15_end:
__sbr_cell_31_16:
    xor eax, eax
__sbr_cell_31_16_end:
__sbr_cell_31_17:
    cmp DWORD PTR [r9+24], 0
__sbr_cell_31_17_end:
__sbr_cell_31_18:
    mov r8d, 0
__sbr_cell_31_18_end:
__sbr_cell_31_19:
    je read_sbr_noise.L6694
__sbr_cell_31_19_end:
read_sbr_noise.L613d:
__sbr_cell_31_20:
    mov QWORD PTR [rbp-64], rdi
__sbr_cell_31_20_end:
__sbr_cell_31_21:
    and r11b, cl
__sbr_cell_31_21_end:
__sbr_cell_31_22:
    and r10b, cl
__sbr_cell_31_22_end:
__sbr_cell_31_23:
    lea rax, [rip+ff_aac_sbr_vlc]
__sbr_cell_31_23_end:
__sbr_cell_31_24:
    movzx ecx, r10b
__sbr_cell_31_24_end:
__sbr_cell_31_25:
    mov rdi, QWORD PTR [rax+rcx*8+64]
__sbr_cell_31_25_end:
__sbr_cell_31_26:
    mov QWORD PTR [rbp-56], rdi
__sbr_cell_31_26_end:
read_sbr_noise.L615b:
__sbr_cell_31_27:
    shl ecx, 4
__sbr_cell_31_27_end:
__sbr_cell_31_28:
    mov r15, QWORD PTR [rcx+rax*1+40]
__sbr_cell_31_28_end:
__sbr_cell_31_29:
    lea rax, [r9+88656]
__sbr_cell_31_29_end:
__sbr_cell_31_30:
    mov QWORD PTR [rbp-72], rax
__sbr_cell_31_30_end:
__sbr_cell_31_31:
    mov BYTE PTR [rbp-41], r11b
__sbr_cell_31_31_end:
read_sbr_noise.L6172:
__sbr_cell_31_32:
    movzx eax, r11b
__sbr_cell_31_32_end:
__sbr_cell_31_33:
    mov DWORD PTR [rbp-48], eax
__sbr_cell_31_33_end:
__sbr_cell_31_34:
    lea r13, [r9+88662]
__sbr_cell_31_34_end:
__sbr_cell_31_35:
    xor r12d, r12d
__sbr_cell_31_35_end:
__sbr_cell_31_36:
    mov QWORD PTR [rbp-80], r9
__sbr_cell_31_36_end:
__sbr_cell_31_37:
    .nops 1
__sbr_cell_31_37_end:
read_sbr_noise.L6190:
__sbr_cell_31_38:
    cmp BYTE PTR [r9+r12*1+37], 0
__sbr_cell_31_38_end:
__sbr_cell_31_39:
    je read_sbr_noise.L64f0
__sbr_cell_31_39_end:
__sbr_cell_31_40:
    cmp DWORD PTR [rsi+311784], 0
__sbr_cell_31_40_end:
__sbr_cell_31_41:
    je read_sbr_noise.L6640
__sbr_cell_31_41_end:
read_sbr_noise.L61a9:
__sbr_cell_31_42:
    lea rbx, [r12+r12*4+0]
__sbr_cell_31_42_end:
__sbr_cell_31_43:
    mov rax, QWORD PTR [rbp-72]
__sbr_cell_31_43_end:
__sbr_cell_31_44:
    movzx edi, BYTE PTR [rax+rbx*1+0]
__sbr_cell_31_44_end:
__sbr_cell_31_45:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_45_end:
__sbr_cell_31_46:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_31_46_end:
__sbr_cell_31_47:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_31_47_end:
__sbr_cell_31_48:
    mov ecx, eax
__sbr_cell_31_48_end:
__sbr_cell_31_49:
    shr ecx, 3
__sbr_cell_31_49_end:
__sbr_cell_31_50:
    mov r9d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_50_end:
__sbr_cell_31_51:
    bswap r9d
__sbr_cell_31_51_end:
__sbr_cell_31_52:
    mov ecx, eax
__sbr_cell_31_52_end:
__sbr_cell_31_53:
    and cl, 7
__sbr_cell_31_53_end:
__sbr_cell_31_54:
    shl r9d, cl
__sbr_cell_31_54_end:
__sbr_cell_31_55:
    shr r9d, 23
__sbr_cell_31_55_end:
read_sbr_noise.L61d7:
__sbr_cell_31_56:
    mov ecx, r9d
__sbr_cell_31_56_end:
__sbr_cell_31_57:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_31_57_end:
__sbr_cell_31_58:
    movzx r9d, WORD PTR [r14+rcx*4+0]
__sbr_cell_31_58_end:
__sbr_cell_31_59:
    movsx r11d, WORD PTR [r14+rcx*4+2]
__sbr_cell_31_59_end:
__sbr_cell_31_60:
    test r11d, r11d
__sbr_cell_31_60_end:
__sbr_cell_31_61:
    jns read_sbr_noise.L6224
__sbr_cell_31_61_end:
read_sbr_noise.L61ee:
__sbr_cell_31_62:
    add eax, 9
__sbr_cell_31_62_end:
__sbr_cell_31_63:
    cmp r8d, eax
__sbr_cell_31_63_end:
__sbr_cell_31_64:
    cmovb eax, r8d
__sbr_cell_31_64_end:
__sbr_cell_31_65:
    movsx r9d, r9w
__sbr_cell_31_65_end:
__sbr_cell_31_66:
    mov ecx, eax
__sbr_cell_31_66_end:
__sbr_cell_31_67:
    shr ecx, 3
__sbr_cell_31_67_end:
__sbr_cell_31_68:
    mov r10d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_68_end:
__sbr_cell_31_69:
    bswap r10d
__sbr_cell_31_69_end:
__sbr_cell_31_70:
    mov ecx, eax
__sbr_cell_31_70_end:
__sbr_cell_31_71:
    and cl, 7
__sbr_cell_31_71_end:
__sbr_cell_31_72:
    shl r10d, cl
__sbr_cell_31_72_end:
read_sbr_noise.L6210:
__sbr_cell_31_73:
    mov ecx, r11d
__sbr_cell_31_73_end:
__sbr_cell_31_74:
    shr r10d, cl
__sbr_cell_31_74_end:
__sbr_cell_31_75:
    add r10d, r9d
__sbr_cell_31_75_end:
__sbr_cell_31_76:
    movzx r9d, WORD PTR [r14+r10*4+0]
__sbr_cell_31_76_end:
__sbr_cell_31_77:
    movsx r11d, WORD PTR [r14+r10*4+2]
__sbr_cell_31_77_end:
read_sbr_noise.L6224:
__sbr_cell_31_78:
    add eax, r11d
__sbr_cell_31_78_end:
__sbr_cell_31_79:
    add rbx, QWORD PTR [rbp-72]
__sbr_cell_31_79_end:
__sbr_cell_31_80:
    cmp r8d, eax
__sbr_cell_31_80_end:
__sbr_cell_31_81:
    cmovb eax, r8d
__sbr_cell_31_81_end:
__sbr_cell_31_82:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_31_82_end:
__sbr_cell_31_83:
    shl r9d, cl
__sbr_cell_31_83_end:
__sbr_cell_31_84:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_84_end:
__sbr_cell_31_85:
    add dil, r9b
__sbr_cell_31_85_end:
__sbr_cell_31_86:
    mov BYTE PTR [rbx+5], dil
__sbr_cell_31_86_end:
__sbr_cell_31_87:
    cmp dil, 31
__sbr_cell_31_87_end:
__sbr_cell_31_88:
    jae read_sbr_noise.L66c9
__sbr_cell_31_88_end:
read_sbr_noise.L624c:
__sbr_cell_31_89:
    cmp DWORD PTR [rsi+311784], 2
__sbr_cell_31_89_end:
__sbr_cell_31_90:
    jb read_sbr_noise.L6640
__sbr_cell_31_90_end:
__sbr_cell_31_91:
    movzx edi, BYTE PTR [rbx+1]
__sbr_cell_31_91_end:
__sbr_cell_31_92:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_92_end:
__sbr_cell_31_93:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_31_93_end:
__sbr_cell_31_94:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_31_94_end:
__sbr_cell_31_95:
    mov ecx, eax
__sbr_cell_31_95_end:
__sbr_cell_31_96:
    shr ecx, 3
__sbr_cell_31_96_end:
__sbr_cell_31_97:
    mov r9d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_97_end:
__sbr_cell_31_98:
    bswap r9d
__sbr_cell_31_98_end:
__sbr_cell_31_99:
    mov ecx, eax
__sbr_cell_31_99_end:
__sbr_cell_31_100:
    and cl, 7
__sbr_cell_31_100_end:
__sbr_cell_31_101:
    shl r9d, cl
__sbr_cell_31_101_end:
__sbr_cell_31_102:
    shr r9d, 23
__sbr_cell_31_102_end:
read_sbr_noise.L627f:
__sbr_cell_31_103:
    mov ecx, r9d
__sbr_cell_31_103_end:
__sbr_cell_31_104:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_31_104_end:
__sbr_cell_31_105:
    movzx r9d, WORD PTR [r14+rcx*4+0]
__sbr_cell_31_105_end:
__sbr_cell_31_106:
    movsx r11d, WORD PTR [r14+rcx*4+2]
__sbr_cell_31_106_end:
__sbr_cell_31_107:
    test r11d, r11d
__sbr_cell_31_107_end:
__sbr_cell_31_108:
    jns read_sbr_noise.L62cc
__sbr_cell_31_108_end:
read_sbr_noise.L6296:
__sbr_cell_31_109:
    add eax, 9
__sbr_cell_31_109_end:
__sbr_cell_31_110:
    cmp r8d, eax
__sbr_cell_31_110_end:
__sbr_cell_31_111:
    cmovb eax, r8d
__sbr_cell_31_111_end:
__sbr_cell_31_112:
    movsx r9d, r9w
__sbr_cell_31_112_end:
__sbr_cell_31_113:
    mov ecx, eax
__sbr_cell_31_113_end:
__sbr_cell_31_114:
    shr ecx, 3
__sbr_cell_31_114_end:
__sbr_cell_31_115:
    mov r10d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_115_end:
__sbr_cell_31_116:
    bswap r10d
__sbr_cell_31_116_end:
__sbr_cell_31_117:
    mov ecx, eax
__sbr_cell_31_117_end:
__sbr_cell_31_118:
    and cl, 7
__sbr_cell_31_118_end:
__sbr_cell_31_119:
    shl r10d, cl
__sbr_cell_31_119_end:
read_sbr_noise.L62b8:
__sbr_cell_31_120:
    mov ecx, r11d
__sbr_cell_31_120_end:
__sbr_cell_31_121:
    shr r10d, cl
__sbr_cell_31_121_end:
__sbr_cell_31_122:
    add r10d, r9d
__sbr_cell_31_122_end:
__sbr_cell_31_123:
    movzx r9d, WORD PTR [r14+r10*4+0]
__sbr_cell_31_123_end:
__sbr_cell_31_124:
    movsx r11d, WORD PTR [r14+r10*4+2]
__sbr_cell_31_124_end:
read_sbr_noise.L62cc:
__sbr_cell_31_125:
    add eax, r11d
__sbr_cell_31_125_end:
__sbr_cell_31_126:
    cmp r8d, eax
__sbr_cell_31_126_end:
__sbr_cell_31_127:
    cmovb eax, r8d
__sbr_cell_31_127_end:
__sbr_cell_31_128:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_31_128_end:
__sbr_cell_31_129:
    shl r9d, cl
__sbr_cell_31_129_end:
__sbr_cell_31_130:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_130_end:
__sbr_cell_31_131:
    add dil, r9b
__sbr_cell_31_131_end:
__sbr_cell_31_132:
    mov BYTE PTR [rbx+6], dil
__sbr_cell_31_132_end:
__sbr_cell_31_133:
    cmp dil, 30
__sbr_cell_31_133_end:
__sbr_cell_31_134:
    ja read_sbr_noise.L66c9
__sbr_cell_31_134_end:
read_sbr_noise.L62f0:
__sbr_cell_31_135:
    cmp DWORD PTR [rsi+311784], 3
__sbr_cell_31_135_end:
__sbr_cell_31_136:
    jb read_sbr_noise.L6640
__sbr_cell_31_136_end:
__sbr_cell_31_137:
    movzx edi, BYTE PTR [rbx+2]
__sbr_cell_31_137_end:
__sbr_cell_31_138:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_138_end:
__sbr_cell_31_139:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_31_139_end:
__sbr_cell_31_140:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_31_140_end:
__sbr_cell_31_141:
    mov ecx, eax
__sbr_cell_31_141_end:
__sbr_cell_31_142:
    shr ecx, 3
__sbr_cell_31_142_end:
__sbr_cell_31_143:
    mov r9d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_143_end:
__sbr_cell_31_144:
    bswap r9d
__sbr_cell_31_144_end:
__sbr_cell_31_145:
    mov ecx, eax
__sbr_cell_31_145_end:
__sbr_cell_31_146:
    and cl, 7
__sbr_cell_31_146_end:
__sbr_cell_31_147:
    shl r9d, cl
__sbr_cell_31_147_end:
__sbr_cell_31_148:
    shr r9d, 23
__sbr_cell_31_148_end:
read_sbr_noise.L6323:
__sbr_cell_31_149:
    mov ecx, r9d
__sbr_cell_31_149_end:
__sbr_cell_31_150:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_31_150_end:
__sbr_cell_31_151:
    movzx r9d, WORD PTR [r14+rcx*4+0]
__sbr_cell_31_151_end:
__sbr_cell_31_152:
    movsx r11d, WORD PTR [r14+rcx*4+2]
__sbr_cell_31_152_end:
__sbr_cell_31_153:
    test r11d, r11d
__sbr_cell_31_153_end:
__sbr_cell_31_154:
    jns read_sbr_noise.L6370
__sbr_cell_31_154_end:
read_sbr_noise.L633a:
__sbr_cell_31_155:
    add eax, 9
__sbr_cell_31_155_end:
__sbr_cell_31_156:
    cmp r8d, eax
__sbr_cell_31_156_end:
__sbr_cell_31_157:
    cmovb eax, r8d
__sbr_cell_31_157_end:
__sbr_cell_31_158:
    movsx r9d, r9w
__sbr_cell_31_158_end:
__sbr_cell_31_159:
    mov ecx, eax
__sbr_cell_31_159_end:
__sbr_cell_31_160:
    shr ecx, 3
__sbr_cell_31_160_end:
__sbr_cell_31_161:
    mov r10d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_161_end:
__sbr_cell_31_162:
    bswap r10d
__sbr_cell_31_162_end:
__sbr_cell_31_163:
    mov ecx, eax
__sbr_cell_31_163_end:
__sbr_cell_31_164:
    and cl, 7
__sbr_cell_31_164_end:
__sbr_cell_31_165:
    shl r10d, cl
__sbr_cell_31_165_end:
read_sbr_noise.L635c:
__sbr_cell_31_166:
    mov ecx, r11d
__sbr_cell_31_166_end:
__sbr_cell_31_167:
    shr r10d, cl
__sbr_cell_31_167_end:
__sbr_cell_31_168:
    add r10d, r9d
__sbr_cell_31_168_end:
__sbr_cell_31_169:
    movzx r9d, WORD PTR [r14+r10*4+0]
__sbr_cell_31_169_end:
__sbr_cell_31_170:
    movsx r11d, WORD PTR [r14+r10*4+2]
__sbr_cell_31_170_end:
read_sbr_noise.L6370:
__sbr_cell_31_171:
    add eax, r11d
__sbr_cell_31_171_end:
__sbr_cell_31_172:
    cmp r8d, eax
__sbr_cell_31_172_end:
__sbr_cell_31_173:
    cmovb eax, r8d
__sbr_cell_31_173_end:
__sbr_cell_31_174:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_31_174_end:
__sbr_cell_31_175:
    shl r9d, cl
__sbr_cell_31_175_end:
__sbr_cell_31_176:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_176_end:
__sbr_cell_31_177:
    add dil, r9b
__sbr_cell_31_177_end:
__sbr_cell_31_178:
    mov BYTE PTR [rbx+7], dil
__sbr_cell_31_178_end:
__sbr_cell_31_179:
    cmp dil, 30
__sbr_cell_31_179_end:
__sbr_cell_31_180:
    ja read_sbr_noise.L66c9
__sbr_cell_31_180_end:
read_sbr_noise.L6394:
__sbr_cell_31_181:
    cmp DWORD PTR [rsi+311784], 4
__sbr_cell_31_181_end:
__sbr_cell_31_182:
    jb read_sbr_noise.L6640
__sbr_cell_31_182_end:
__sbr_cell_31_183:
    movzx edi, BYTE PTR [rbx+3]
__sbr_cell_31_183_end:
__sbr_cell_31_184:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_184_end:
__sbr_cell_31_185:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_31_185_end:
__sbr_cell_31_186:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_31_186_end:
__sbr_cell_31_187:
    mov ecx, eax
__sbr_cell_31_187_end:
__sbr_cell_31_188:
    shr ecx, 3
__sbr_cell_31_188_end:
__sbr_cell_31_189:
    mov r9d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_189_end:
__sbr_cell_31_190:
    bswap r9d
__sbr_cell_31_190_end:
__sbr_cell_31_191:
    mov ecx, eax
__sbr_cell_31_191_end:
__sbr_cell_31_192:
    and cl, 7
__sbr_cell_31_192_end:
__sbr_cell_31_193:
    shl r9d, cl
__sbr_cell_31_193_end:
__sbr_cell_31_194:
    shr r9d, 23
__sbr_cell_31_194_end:
read_sbr_noise.L63c7:
__sbr_cell_31_195:
    mov ecx, r9d
__sbr_cell_31_195_end:
__sbr_cell_31_196:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_31_196_end:
__sbr_cell_31_197:
    movzx r9d, WORD PTR [r14+rcx*4+0]
__sbr_cell_31_197_end:
__sbr_cell_31_198:
    movsx r11d, WORD PTR [r14+rcx*4+2]
__sbr_cell_31_198_end:
__sbr_cell_31_199:
    test r11d, r11d
__sbr_cell_31_199_end:
__sbr_cell_31_200:
    jns read_sbr_noise.L6414
__sbr_cell_31_200_end:
read_sbr_noise.L63de:
__sbr_cell_31_201:
    add eax, 9
__sbr_cell_31_201_end:
__sbr_cell_31_202:
    cmp r8d, eax
__sbr_cell_31_202_end:
__sbr_cell_31_203:
    cmovb eax, r8d
__sbr_cell_31_203_end:
__sbr_cell_31_204:
    movsx r9d, r9w
__sbr_cell_31_204_end:
__sbr_cell_31_205:
    mov ecx, eax
__sbr_cell_31_205_end:
__sbr_cell_31_206:
    shr ecx, 3
__sbr_cell_31_206_end:
__sbr_cell_31_207:
    mov r10d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_207_end:
__sbr_cell_31_208:
    bswap r10d
__sbr_cell_31_208_end:
__sbr_cell_31_209:
    mov ecx, eax
__sbr_cell_31_209_end:
__sbr_cell_31_210:
    and cl, 7
__sbr_cell_31_210_end:
__sbr_cell_31_211:
    shl r10d, cl
__sbr_cell_31_211_end:
read_sbr_noise.L6400:
__sbr_cell_31_212:
    mov ecx, r11d
__sbr_cell_31_212_end:
__sbr_cell_31_213:
    shr r10d, cl
__sbr_cell_31_213_end:
__sbr_cell_31_214:
    add r10d, r9d
__sbr_cell_31_214_end:
__sbr_cell_31_215:
    movzx r9d, WORD PTR [r14+r10*4+0]
__sbr_cell_31_215_end:
__sbr_cell_31_216:
    movsx r11d, WORD PTR [r14+r10*4+2]
__sbr_cell_31_216_end:
read_sbr_noise.L6414:
__sbr_cell_31_217:
    add eax, r11d
__sbr_cell_31_217_end:
__sbr_cell_31_218:
    cmp r8d, eax
__sbr_cell_31_218_end:
__sbr_cell_31_219:
    cmovb eax, r8d
__sbr_cell_31_219_end:
__sbr_cell_31_220:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_31_220_end:
__sbr_cell_31_221:
    shl r9d, cl
__sbr_cell_31_221_end:
__sbr_cell_31_222:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_222_end:
__sbr_cell_31_223:
    add dil, r9b
__sbr_cell_31_223_end:
__sbr_cell_31_224:
    mov BYTE PTR [rbx+8], dil
__sbr_cell_31_224_end:
__sbr_cell_31_225:
    cmp dil, 30
__sbr_cell_31_225_end:
__sbr_cell_31_226:
    ja read_sbr_noise.L66c9
__sbr_cell_31_226_end:
read_sbr_noise.L6438:
__sbr_cell_31_227:
    cmp DWORD PTR [rsi+311784], 5
__sbr_cell_31_227_end:
__sbr_cell_31_228:
    jb read_sbr_noise.L6640
__sbr_cell_31_228_end:
__sbr_cell_31_229:
    movzx edi, BYTE PTR [rbx+4]
__sbr_cell_31_229_end:
__sbr_cell_31_230:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_230_end:
__sbr_cell_31_231:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_31_231_end:
__sbr_cell_31_232:
    mov r10, QWORD PTR [rdx+0]
__sbr_cell_31_232_end:
__sbr_cell_31_233:
    mov ecx, eax
__sbr_cell_31_233_end:
__sbr_cell_31_234:
    shr ecx, 3
__sbr_cell_31_234_end:
__sbr_cell_31_235:
    mov r9d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_235_end:
__sbr_cell_31_236:
    bswap r9d
__sbr_cell_31_236_end:
__sbr_cell_31_237:
    mov ecx, eax
__sbr_cell_31_237_end:
__sbr_cell_31_238:
    and cl, 7
__sbr_cell_31_238_end:
__sbr_cell_31_239:
    shl r9d, cl
__sbr_cell_31_239_end:
__sbr_cell_31_240:
    shr r9d, 23
__sbr_cell_31_240_end:
read_sbr_noise.L646b:
__sbr_cell_31_241:
    mov ecx, r9d
__sbr_cell_31_241_end:
__sbr_cell_31_242:
    mov r14, QWORD PTR [rbp-56]
__sbr_cell_31_242_end:
__sbr_cell_31_243:
    movzx r9d, WORD PTR [r14+rcx*4+0]
__sbr_cell_31_243_end:
__sbr_cell_31_244:
    movsx r11d, WORD PTR [r14+rcx*4+2]
__sbr_cell_31_244_end:
__sbr_cell_31_245:
    test r11d, r11d
__sbr_cell_31_245_end:
__sbr_cell_31_246:
    jns read_sbr_noise.L64b8
__sbr_cell_31_246_end:
read_sbr_noise.L6482:
__sbr_cell_31_247:
    add eax, 9
__sbr_cell_31_247_end:
__sbr_cell_31_248:
    cmp r8d, eax
__sbr_cell_31_248_end:
__sbr_cell_31_249:
    cmovb eax, r8d
__sbr_cell_31_249_end:
__sbr_cell_31_250:
    movsx r9d, r9w
__sbr_cell_31_250_end:
__sbr_cell_31_251:
    mov ecx, eax
__sbr_cell_31_251_end:
__sbr_cell_31_252:
    shr ecx, 3
__sbr_cell_31_252_end:
__sbr_cell_31_253:
    mov r10d, DWORD PTR [r10+rcx*1+0]
__sbr_cell_31_253_end:
__sbr_cell_31_254:
    bswap r10d
__sbr_cell_31_254_end:
__sbr_cell_31_255:
    mov ecx, eax
__sbr_cell_31_255_end:
__sbr_cell_31_256:
    and cl, 7
__sbr_cell_31_256_end:
__sbr_cell_31_257:
    shl r10d, cl
__sbr_cell_31_257_end:
read_sbr_noise.L64a4:
__sbr_cell_31_258:
    mov ecx, r11d
__sbr_cell_31_258_end:
__sbr_cell_31_259:
    shr r10d, cl
__sbr_cell_31_259_end:
__sbr_cell_31_260:
    add r10d, r9d
__sbr_cell_31_260_end:
__sbr_cell_31_261:
    movzx r9d, WORD PTR [r14+r10*4+0]
__sbr_cell_31_261_end:
__sbr_cell_31_262:
    movsx r11d, WORD PTR [r14+r10*4+2]
__sbr_cell_31_262_end:
read_sbr_noise.L64b8:
__sbr_cell_31_263:
    add eax, r11d
__sbr_cell_31_263_end:
__sbr_cell_31_264:
    cmp r8d, eax
__sbr_cell_31_264_end:
__sbr_cell_31_265:
    cmovb eax, r8d
__sbr_cell_31_265_end:
__sbr_cell_31_266:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_31_266_end:
__sbr_cell_31_267:
    shl r9d, cl
__sbr_cell_31_267_end:
__sbr_cell_31_268:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_268_end:
__sbr_cell_31_269:
    add dil, r9b
__sbr_cell_31_269_end:
__sbr_cell_31_270:
    mov BYTE PTR [rbx+9], dil
__sbr_cell_31_270_end:
__sbr_cell_31_271:
    cmp dil, 30
__sbr_cell_31_271_end:
__sbr_cell_31_272:
    ja read_sbr_noise.L66c9
__sbr_cell_31_272_end:
read_sbr_noise.L64dc:
__sbr_cell_31_273:
    cmp DWORD PTR [rsi+311784], 6
__sbr_cell_31_273_end:
__sbr_cell_31_274:
    jb read_sbr_noise.L6640
__sbr_cell_31_274_end:
__sbr_cell_31_275:
    jmp read_sbr_noise.L66d9
__sbr_cell_31_275_end:
__sbr_cell_31_276:
    .nops 1
__sbr_cell_31_276_end:
read_sbr_noise.L64f0:
__sbr_cell_31_277:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_277_end:
__sbr_cell_31_278:
    mov edi, DWORD PTR [rdx+16]
__sbr_cell_31_278_end:
__sbr_cell_31_279:
    mov rcx, QWORD PTR [rdx+0]
__sbr_cell_31_279_end:
__sbr_cell_31_280:
    mov r8d, eax
__sbr_cell_31_280_end:
__sbr_cell_31_281:
    shr r8d, 3
__sbr_cell_31_281_end:
__sbr_cell_31_282:
    mov r8d, DWORD PTR [rcx+r8*1+0]
__sbr_cell_31_282_end:
__sbr_cell_31_283:
    bswap r8d
__sbr_cell_31_283_end:
__sbr_cell_31_284:
    mov ecx, eax
__sbr_cell_31_284_end:
__sbr_cell_31_285:
    and cl, 7
__sbr_cell_31_285_end:
__sbr_cell_31_286:
    shl r8d, cl
__sbr_cell_31_286_end:
__sbr_cell_31_287:
    shr r8d, 27
__sbr_cell_31_287_end:
__sbr_cell_31_288:
    add eax, 5
__sbr_cell_31_288_end:
__sbr_cell_31_289:
    cmp edi, eax
__sbr_cell_31_289_end:
__sbr_cell_31_290:
    cmovb eax, edi
__sbr_cell_31_290_end:
read_sbr_noise.L651b:
__sbr_cell_31_291:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_291_end:
__sbr_cell_31_292:
    movzx ecx, BYTE PTR [rbp-41]
__sbr_cell_31_292_end:
__sbr_cell_31_293:
    shl r8d, cl
__sbr_cell_31_293_end:
__sbr_cell_31_294:
    lea rax, [r12+r12*4+0]
__sbr_cell_31_294_end:
__sbr_cell_31_295:
    mov BYTE PTR [r9+rax*1+88661], r8b
__sbr_cell_31_295_end:
__sbr_cell_31_296:
    cmp DWORD PTR [rsi+311784], 2
__sbr_cell_31_296_end:
__sbr_cell_31_297:
    jb read_sbr_noise.L6640
__sbr_cell_31_297_end:
__sbr_cell_31_298:
    xor edi, edi
__sbr_cell_31_298_end:
read_sbr_noise.L6540:
__sbr_cell_31_299:
    movzx r9d, BYTE PTR [r13+rdi*1-1]
__sbr_cell_31_299_end:
__sbr_cell_31_300:
    mov eax, DWORD PTR [rdx+8]
__sbr_cell_31_300_end:
__sbr_cell_31_301:
    mov r8d, DWORD PTR [rdx+16]
__sbr_cell_31_301_end:
__sbr_cell_31_302:
    mov r14, QWORD PTR [rdx+0]
__sbr_cell_31_302_end:
__sbr_cell_31_303:
    mov ecx, eax
__sbr_cell_31_303_end:
__sbr_cell_31_304:
    shr ecx, 3
__sbr_cell_31_304_end:
__sbr_cell_31_305:
    mov r10d, DWORD PTR [r14+rcx*1+0]
__sbr_cell_31_305_end:
__sbr_cell_31_306:
    bswap r10d
__sbr_cell_31_306_end:
__sbr_cell_31_307:
    mov ecx, eax
__sbr_cell_31_307_end:
__sbr_cell_31_308:
    and cl, 7
__sbr_cell_31_308_end:
__sbr_cell_31_309:
    shl r10d, cl
__sbr_cell_31_309_end:
__sbr_cell_31_310:
    shr r10d, 23
__sbr_cell_31_310_end:
read_sbr_noise.L6568:
__sbr_cell_31_311:
    mov ecx, r10d
__sbr_cell_31_311_end:
__sbr_cell_31_312:
    movzx r10d, WORD PTR [r15+rcx*4+0]
__sbr_cell_31_312_end:
__sbr_cell_31_313:
    movsx r11d, WORD PTR [r15+rcx*4+2]
__sbr_cell_31_313_end:
__sbr_cell_31_314:
    test r11d, r11d
__sbr_cell_31_314_end:
__sbr_cell_31_315:
    jns read_sbr_noise.L65f0
__sbr_cell_31_315_end:
read_sbr_noise.L657b:
__sbr_cell_31_316:
    movsx r10d, r10w
__sbr_cell_31_316_end:
__sbr_cell_31_317:
    add eax, 9
__sbr_cell_31_317_end:
__sbr_cell_31_318:
    cmp r8d, eax
__sbr_cell_31_318_end:
__sbr_cell_31_319:
    cmovb eax, r8d
__sbr_cell_31_319_end:
__sbr_cell_31_320:
    mov ecx, eax
__sbr_cell_31_320_end:
__sbr_cell_31_321:
    shr ecx, 3
__sbr_cell_31_321_end:
__sbr_cell_31_322:
    mov ebx, DWORD PTR [r14+rcx*1+0]
__sbr_cell_31_322_end:
__sbr_cell_31_323:
    bswap ebx
__sbr_cell_31_323_end:
__sbr_cell_31_324:
    mov ecx, eax
__sbr_cell_31_324_end:
__sbr_cell_31_325:
    and cl, 7
__sbr_cell_31_325_end:
__sbr_cell_31_326:
    shl ebx, cl
__sbr_cell_31_326_end:
read_sbr_noise.L659b:
__sbr_cell_31_327:
    mov ecx, r11d
__sbr_cell_31_327_end:
__sbr_cell_31_328:
    shr ebx, cl
__sbr_cell_31_328_end:
__sbr_cell_31_329:
    add ebx, r10d
__sbr_cell_31_329_end:
__sbr_cell_31_330:
    movzx r10d, WORD PTR [r15+rbx*4+0]
__sbr_cell_31_330_end:
__sbr_cell_31_331:
    movsx ebx, WORD PTR [r15+rbx*4+2]
__sbr_cell_31_331_end:
__sbr_cell_31_332:
    test ebx, ebx
__sbr_cell_31_332_end:
__sbr_cell_31_333:
    js read_sbr_noise.L65b7
__sbr_cell_31_333_end:
__sbr_cell_31_334:
    mov r11d, ebx
__sbr_cell_31_334_end:
__sbr_cell_31_335:
    jmp read_sbr_noise.L65f0
__sbr_cell_31_335_end:
read_sbr_noise.L65b7:
__sbr_cell_31_336:
    sub eax, r11d
__sbr_cell_31_336_end:
__sbr_cell_31_337:
    cmp r8d, eax
__sbr_cell_31_337_end:
__sbr_cell_31_338:
    cmovb eax, r8d
__sbr_cell_31_338_end:
__sbr_cell_31_339:
    movsx r10d, r10w
__sbr_cell_31_339_end:
__sbr_cell_31_340:
    mov ecx, eax
__sbr_cell_31_340_end:
__sbr_cell_31_341:
    shr ecx, 3
__sbr_cell_31_341_end:
__sbr_cell_31_342:
    mov r11d, DWORD PTR [r14+rcx*1+0]
__sbr_cell_31_342_end:
__sbr_cell_31_343:
    bswap r11d
__sbr_cell_31_343_end:
__sbr_cell_31_344:
    mov ecx, eax
__sbr_cell_31_344_end:
__sbr_cell_31_345:
    and cl, 7
__sbr_cell_31_345_end:
__sbr_cell_31_346:
    shl r11d, cl
__sbr_cell_31_346_end:
read_sbr_noise.L65d9:
__sbr_cell_31_347:
    mov ecx, ebx
__sbr_cell_31_347_end:
__sbr_cell_31_348:
    shr r11d, cl
__sbr_cell_31_348_end:
__sbr_cell_31_349:
    add r11d, r10d
__sbr_cell_31_349_end:
__sbr_cell_31_350:
    movzx r10d, WORD PTR [r15+r11*4+0]
__sbr_cell_31_350_end:
__sbr_cell_31_351:
    movsx r11d, WORD PTR [r15+r11*4+2]
__sbr_cell_31_351_end:
__sbr_cell_31_352:
    .nops 1
__sbr_cell_31_352_end:
read_sbr_noise.L65f0:
__sbr_cell_31_353:
    add eax, r11d
__sbr_cell_31_353_end:
__sbr_cell_31_354:
    cmp r8d, eax
__sbr_cell_31_354_end:
__sbr_cell_31_355:
    cmovb eax, r8d
__sbr_cell_31_355_end:
__sbr_cell_31_356:
    mov DWORD PTR [rdx+8], eax
__sbr_cell_31_356_end:
__sbr_cell_31_357:
    cmp rdi, 4
__sbr_cell_31_357_end:
__sbr_cell_31_358:
    je read_sbr_noise.L66cf
__sbr_cell_31_358_end:
read_sbr_noise.L6607:
__sbr_cell_31_359:
    mov ecx, DWORD PTR [rbp-48]
__sbr_cell_31_359_end:
__sbr_cell_31_360:
    shl r10d, cl
__sbr_cell_31_360_end:
__sbr_cell_31_361:
    add r9b, r10b
__sbr_cell_31_361_end:
__sbr_cell_31_362:
    mov BYTE PTR [r13+rdi*1+0], r9b
__sbr_cell_31_362_end:
__sbr_cell_31_363:
    cmp r9b, 31
__sbr_cell_31_363_end:
__sbr_cell_31_364:
    jae read_sbr_noise.L6663
__sbr_cell_31_364_end:
__sbr_cell_31_365:
    mov eax, DWORD PTR [rsi+311784]
__sbr_cell_31_365_end:
__sbr_cell_31_366:
    lea rcx, [rdi+1]
__sbr_cell_31_366_end:
__sbr_cell_31_367:
    add rdi, 2
__sbr_cell_31_367_end:
__sbr_cell_31_368:
    cmp rdi, rax
__sbr_cell_31_368_end:
__sbr_cell_31_369:
    mov rdi, rcx
__sbr_cell_31_369_end:
__sbr_cell_31_370:
    jb read_sbr_noise.L6540
__sbr_cell_31_370_end:
__sbr_cell_31_371:
    .nops 1
__sbr_cell_31_371_end:
read_sbr_noise.L6640:
__sbr_cell_31_372:
    inc r12
__sbr_cell_31_372_end:
__sbr_cell_31_373:
    mov r9, QWORD PTR [rbp-80]
__sbr_cell_31_373_end:
__sbr_cell_31_374:
    mov r8d, DWORD PTR [r9+24]
__sbr_cell_31_374_end:
__sbr_cell_31_375:
    cmp r12, r8
__sbr_cell_31_375_end:
__sbr_cell_31_376:
    jae read_sbr_noise.L6689
__sbr_cell_31_376_end:
__sbr_cell_31_377:
    add r13, 5
__sbr_cell_31_377_end:
__sbr_cell_31_378:
    cmp r12, 2
__sbr_cell_31_378_end:
__sbr_cell_31_379:
    jne read_sbr_noise.L6190
__sbr_cell_31_379_end:
__sbr_cell_31_380:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_31_380_end:
read_sbr_noise.L6663:
__sbr_cell_31_381:
    movzx ecx, r9b
__sbr_cell_31_381_end:
read_sbr_noise.L6667:
__sbr_cell_31_382:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_31_382_end:
__sbr_cell_31_383:
    mov rdi, QWORD PTR [rax+8]
__sbr_cell_31_383_end:
__sbr_cell_31_384:
    lea rdx, [rip+L_str_31]
__sbr_cell_31_384_end:
__sbr_cell_31_385:
    mov esi, 16
__sbr_cell_31_385_end:
__sbr_cell_31_386:
    xor eax, eax
__sbr_cell_31_386_end:
__sbr_cell_31_387:
    call av_log
__sbr_cell_31_387_end:
__sbr_cell_31_388:
    mov eax, 3199971767
__sbr_cell_31_388_end:
__sbr_cell_31_389:
    jmp read_sbr_noise.L66ba
__sbr_cell_31_389_end:
read_sbr_noise.L6689:
__sbr_cell_31_390:
    cmp r8d, 4
__sbr_cell_31_390_end:
__sbr_cell_31_391:
    mov eax, 0
__sbr_cell_31_391_end:
__sbr_cell_31_392:
    jae read_sbr_noise.L66d4
__sbr_cell_31_392_end:
read_sbr_noise.L6694:
__sbr_cell_31_393:
    mov ecx, r8d
__sbr_cell_31_393_end:
__sbr_cell_31_394:
    lea rdx, [rcx+rcx*4+0]
__sbr_cell_31_394_end:
__sbr_cell_31_395:
    movzx ecx, BYTE PTR [r9+rdx*1+88660]
__sbr_cell_31_395_end:
__sbr_cell_31_396:
    mov BYTE PTR [r9+88660], cl
__sbr_cell_31_396_end:
__sbr_cell_31_397:
    mov ecx, DWORD PTR [r9+rdx*1+88656]
__sbr_cell_31_397_end:
__sbr_cell_31_398:
    mov DWORD PTR [r9+88656], ecx
__sbr_cell_31_398_end:
read_sbr_noise.L66ba:
__sbr_cell_31_399:
    add rsp, 40
__sbr_cell_31_399_end:
__sbr_cell_31_400:
    pop rbx
__sbr_cell_31_400_end:
__sbr_cell_31_401:
    pop r12
__sbr_cell_31_401_end:
__sbr_cell_31_402:
    pop r13
__sbr_cell_31_402_end:
__sbr_cell_31_403:
    pop r14
__sbr_cell_31_403_end:
__sbr_cell_31_404:
    pop r15
__sbr_cell_31_404_end:
__sbr_cell_31_405:
    pop rbp
__sbr_cell_31_405_end:
read_sbr_noise.done:
__sbr_cell_31_406:
    ret
__sbr_cell_31_406_end:
read_sbr_noise.L66c9:
__sbr_cell_31_407:
    movzx ecx, dil
__sbr_cell_31_407_end:
__sbr_cell_31_408:
    jmp read_sbr_noise.L6667
__sbr_cell_31_408_end:
read_sbr_noise.L66cf:
__sbr_cell_31_409:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_31_409_end:
read_sbr_noise.L66d4:
__sbr_cell_31_410:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_31_410_end:
read_sbr_noise.L66d9:
__sbr_cell_31_411:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_31_411_end:
__sbr_cell_31_412:
    int3
__sbr_cell_31_412_end:
__sbr_cell_31_413:
    int3
__sbr_cell_31_413_end:
.size read_sbr_noise, .-read_sbr_noise
.section .text.sbr_hf_assemble,"ax",@progbits
.globl sbr_hf_assemble
.type sbr_hf_assemble,@function
sbr_hf_assemble:
__sbr_cell_32_0:
    push rbp
__sbr_cell_32_0_end:
__sbr_cell_32_1:
    mov rbp, rsp
__sbr_cell_32_1_end:
__sbr_cell_32_2:
    push r15
__sbr_cell_32_2_end:
__sbr_cell_32_3:
    push r14
__sbr_cell_32_3_end:
__sbr_cell_32_4:
    push r13
__sbr_cell_32_4_end:
__sbr_cell_32_5:
    push r12
__sbr_cell_32_5_end:
__sbr_cell_32_6:
    push rbx
__sbr_cell_32_6_end:
__sbr_cell_32_7:
    sub rsp, 600
__sbr_cell_32_7_end:
sbr_hf_assemble.p1:
__sbr_cell_32_8:
    mov QWORD PTR [rbp-144], r8
__sbr_cell_32_8_end:
__sbr_cell_32_9:
    mov r8, rcx
__sbr_cell_32_9_end:
__sbr_cell_32_10:
    mov QWORD PTR [rbp-192], rsi
__sbr_cell_32_10_end:
__sbr_cell_32_11:
    mov QWORD PTR [rbp-128], rdi
__sbr_cell_32_11_end:
__sbr_cell_32_12:
    mov r14d, DWORD PTR [rdx+56]
__sbr_cell_32_12_end:
__sbr_cell_32_13:
    xor r9d, r9d
__sbr_cell_32_13_end:
__sbr_cell_32_14:
    test r14d, r14d
__sbr_cell_32_14_end:
__sbr_cell_32_15:
    sete r10b
__sbr_cell_32_15_end:
__sbr_cell_32_16:
    movsxd rax, DWORD PTR [rdx+88]
__sbr_cell_32_16_end:
__sbr_cell_32_17:
    mov QWORD PTR [rbp-136], rax
__sbr_cell_32_17_end:
__sbr_cell_32_18:
    movsxd rax, DWORD PTR [rdx+96]
__sbr_cell_32_18_end:
__sbr_cell_32_19:
    mov QWORD PTR [rbp-120], rax
__sbr_cell_32_19_end:
sbr_hf_assemble.p2:
__sbr_cell_32_20:
    lea rax, [rcx+69936]
__sbr_cell_32_20_end:
__sbr_cell_32_21:
    mov QWORD PTR [rbp-152], rax
__sbr_cell_32_21_end:
__sbr_cell_32_22:
    lea rax, [rcx+78000]
__sbr_cell_32_22_end:
__sbr_cell_32_23:
    mov QWORD PTR [rbp-176], rax
__sbr_cell_32_23_end:
__sbr_cell_32_24:
    vmovq xmm4, QWORD PTR [rcx+88748]
__sbr_cell_32_24_end:
__sbr_cell_32_25:
    mov QWORD PTR [rbp-64], rdx
__sbr_cell_32_25_end:
__sbr_cell_32_26:
    cmp DWORD PTR [rdx+24], 0
__sbr_cell_32_26_end:
__sbr_cell_32_27:
    mov QWORD PTR [rbp-48], rcx
__sbr_cell_32_27_end:
__sbr_cell_32_28:
    je sbr_hf_assemble.La8e1
__sbr_cell_32_28_end:
__sbr_cell_32_29:
    test r14d, r14d
__sbr_cell_32_29_end:
__sbr_cell_32_30:
    jne sbr_hf_assemble.La8ea
__sbr_cell_32_30_end:
sbr_hf_assemble.r0:
__sbr_cell_32_31:
    mov DWORD PTR [rbp-84], r14d
__sbr_cell_32_31_end:
__sbr_cell_32_32:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_32_32_end:
__sbr_cell_32_33:
    lea r13, [rax+387776]
__sbr_cell_32_33_end:
__sbr_cell_32_34:
    mov rcx, QWORD PTR [rbp-120]
__sbr_cell_32_34_end:
__sbr_cell_32_35:
    lea r12, [rcx*4+0]
__sbr_cell_32_35_end:
__sbr_cell_32_36:
    lea r14, [rax+390848]
__sbr_cell_32_36_end:
__sbr_cell_32_37:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_37_end:
__sbr_cell_32_38:
    lea rdi, [rax+rax*2+0]
__sbr_cell_32_38_end:
__sbr_cell_32_39:
    shl edi, 7
__sbr_cell_32_39_end:
__sbr_cell_32_40:
    mov rbx, QWORD PTR [rbp-152]
__sbr_cell_32_40_end:
__sbr_cell_32_41:
    add rdi, rbx
__sbr_cell_32_41_end:
__sbr_cell_32_42:
    mov rsi, r14
__sbr_cell_32_42_end:
__sbr_cell_32_43:
    mov rdx, r12
__sbr_cell_32_43_end:
__sbr_cell_32_44:
    vmovdqa XMMWORD PTR [rbp-112], xmm4
__sbr_cell_32_44_end:
__sbr_cell_32_45:
    mov BYTE PTR [rbp-56], r10b
__sbr_cell_32_45_end:
sbr_hf_assemble.r0c:
__sbr_cell_32_46:
    call memcpy
__sbr_cell_32_46_end:
sbr_hf_assemble.r1:
__sbr_cell_32_47:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_47_end:
__sbr_cell_32_48:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_48_end:
__sbr_cell_32_49:
    lea rdi, [rax+rax*2+0]
__sbr_cell_32_49_end:
__sbr_cell_32_50:
    shl edi, 7
__sbr_cell_32_50_end:
__sbr_cell_32_51:
    mov r15, QWORD PTR [rbp-176]
__sbr_cell_32_51_end:
__sbr_cell_32_52:
    add rdi, r15
__sbr_cell_32_52_end:
__sbr_cell_32_53:
    mov rsi, r13
__sbr_cell_32_53_end:
__sbr_cell_32_54:
    mov rdx, r12
__sbr_cell_32_54_end:
sbr_hf_assemble.r1c:
__sbr_cell_32_55:
    call memcpy
__sbr_cell_32_55_end:
sbr_hf_assemble.r2:
__sbr_cell_32_56:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_56_end:
__sbr_cell_32_57:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_57_end:
__sbr_cell_32_58:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_58_end:
__sbr_cell_32_59:
    shl eax, 7
__sbr_cell_32_59_end:
__sbr_cell_32_60:
    lea rdi, [rbx+rax*1+0]
__sbr_cell_32_60_end:
__sbr_cell_32_61:
    add rdi, 192
__sbr_cell_32_61_end:
__sbr_cell_32_62:
    mov rsi, r14
__sbr_cell_32_62_end:
__sbr_cell_32_63:
    mov rdx, r12
__sbr_cell_32_63_end:
sbr_hf_assemble.r2c:
__sbr_cell_32_64:
    call memcpy
__sbr_cell_32_64_end:
sbr_hf_assemble.r3:
__sbr_cell_32_65:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_65_end:
__sbr_cell_32_66:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_66_end:
__sbr_cell_32_67:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_67_end:
__sbr_cell_32_68:
    shl eax, 7
__sbr_cell_32_68_end:
__sbr_cell_32_69:
    lea rdi, [r15+rax*1+0]
__sbr_cell_32_69_end:
__sbr_cell_32_70:
    add rdi, 192
__sbr_cell_32_70_end:
__sbr_cell_32_71:
    mov rsi, r13
__sbr_cell_32_71_end:
__sbr_cell_32_72:
    mov rdx, r12
__sbr_cell_32_72_end:
sbr_hf_assemble.r3c:
__sbr_cell_32_73:
    call memcpy
__sbr_cell_32_73_end:
sbr_hf_assemble.r4:
__sbr_cell_32_74:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_74_end:
__sbr_cell_32_75:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_75_end:
__sbr_cell_32_76:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_76_end:
__sbr_cell_32_77:
    shl eax, 7
__sbr_cell_32_77_end:
__sbr_cell_32_78:
    lea rdi, [rbx+rax*1+0]
__sbr_cell_32_78_end:
__sbr_cell_32_79:
    add rdi, 384
__sbr_cell_32_79_end:
__sbr_cell_32_80:
    mov rsi, r14
__sbr_cell_32_80_end:
__sbr_cell_32_81:
    mov rdx, r12
__sbr_cell_32_81_end:
sbr_hf_assemble.r4c:
__sbr_cell_32_82:
    call memcpy
__sbr_cell_32_82_end:
sbr_hf_assemble.r5:
__sbr_cell_32_83:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_83_end:
__sbr_cell_32_84:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_84_end:
__sbr_cell_32_85:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_85_end:
__sbr_cell_32_86:
    shl eax, 7
__sbr_cell_32_86_end:
__sbr_cell_32_87:
    lea rdi, [r15+rax*1+0]
__sbr_cell_32_87_end:
__sbr_cell_32_88:
    add rdi, 384
__sbr_cell_32_88_end:
__sbr_cell_32_89:
    mov rsi, r13
__sbr_cell_32_89_end:
__sbr_cell_32_90:
    mov rdx, r12
__sbr_cell_32_90_end:
sbr_hf_assemble.r5c:
__sbr_cell_32_91:
    call memcpy
__sbr_cell_32_91_end:
sbr_hf_assemble.r6:
__sbr_cell_32_92:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_92_end:
__sbr_cell_32_93:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_93_end:
__sbr_cell_32_94:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_94_end:
__sbr_cell_32_95:
    shl eax, 7
__sbr_cell_32_95_end:
__sbr_cell_32_96:
    lea rdi, [rbx+rax*1+0]
__sbr_cell_32_96_end:
__sbr_cell_32_97:
    add rdi, 576
__sbr_cell_32_97_end:
__sbr_cell_32_98:
    mov rsi, r14
__sbr_cell_32_98_end:
__sbr_cell_32_99:
    mov rdx, r12
__sbr_cell_32_99_end:
sbr_hf_assemble.r6c:
__sbr_cell_32_100:
    call memcpy
__sbr_cell_32_100_end:
sbr_hf_assemble.r7:
__sbr_cell_32_101:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_32_101_end:
__sbr_cell_32_102:
    movzx eax, BYTE PTR [rax+88732]
__sbr_cell_32_102_end:
__sbr_cell_32_103:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_103_end:
__sbr_cell_32_104:
    shl eax, 7
__sbr_cell_32_104_end:
__sbr_cell_32_105:
    lea rdi, [r15+rax*1+0]
__sbr_cell_32_105_end:
__sbr_cell_32_106:
    add rdi, 576
__sbr_cell_32_106_end:
__sbr_cell_32_107:
    mov rsi, r13
__sbr_cell_32_107_end:
__sbr_cell_32_108:
    mov rdx, r12
__sbr_cell_32_108_end:
sbr_hf_assemble.r7c:
__sbr_cell_32_109:
    call memcpy
__sbr_cell_32_109_end:
sbr_hf_assemble.r8:
__sbr_cell_32_110:
    movzx r10d, BYTE PTR [rbp-56]
__sbr_cell_32_110_end:
__sbr_cell_32_111:
    xor r9d, r9d
__sbr_cell_32_111_end:
__sbr_cell_32_112:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_112_end:
__sbr_cell_32_113:
    mov r14d, DWORD PTR [rbp-84]
__sbr_cell_32_113_end:
__sbr_cell_32_114:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_114_end:
__sbr_cell_32_115:
    mov edx, DWORD PTR [r8+8]
__sbr_cell_32_115_end:
__sbr_cell_32_116:
    test edx, edx
__sbr_cell_32_116_end:
__sbr_cell_32_117:
    jne sbr_hf_assemble.La8f6
__sbr_cell_32_117_end:
__sbr_cell_32_118:
    jmp sbr_hf_assemble.Lb820
__sbr_cell_32_118_end:
sbr_hf_assemble.La8e1:
__sbr_cell_32_119:
    test r14d, r14d
__sbr_cell_32_119_end:
__sbr_cell_32_120:
    je sbr_hf_assemble.Lb426
__sbr_cell_32_120_end:
sbr_hf_assemble.La8ea:
__sbr_cell_32_121:
    mov edx, DWORD PTR [r8+8]
__sbr_cell_32_121_end:
__sbr_cell_32_122:
    test edx, edx
__sbr_cell_32_122_end:
__sbr_cell_32_123:
    je sbr_hf_assemble.Lb820
__sbr_cell_32_123_end:
sbr_hf_assemble.La8f6:
__sbr_cell_32_124:
    mov DWORD PTR [rbp-84], r14d
__sbr_cell_32_124_end:
__sbr_cell_32_125:
    mov r9b, r10b
__sbr_cell_32_125_end:
__sbr_cell_32_126:
    shl r9d, 2
__sbr_cell_32_126_end:
__sbr_cell_32_127:
    mov rax, QWORD PTR [rbp-120]
__sbr_cell_32_127_end:
__sbr_cell_32_128:
    lea r13, [rax*4+0]
__sbr_cell_32_128_end:
__sbr_cell_32_129:
    mov esi, r9d
__sbr_cell_32_129_end:
__sbr_cell_32_130:
    movzx ecx, BYTE PTR [r8+88732]
__sbr_cell_32_130_end:
__sbr_cell_32_131:
    movzx eax, BYTE PTR [r8+88733]
__sbr_cell_32_131_end:
__sbr_cell_32_132:
    cmp cl, al
__sbr_cell_32_132_end:
__sbr_cell_32_133:
    vmovdqa XMMWORD PTR [rbp-112], xmm4
__sbr_cell_32_133_end:
__sbr_cell_32_134:
    mov DWORD PTR [rbp-56], edx
__sbr_cell_32_134_end:
__sbr_cell_32_135:
    mov QWORD PTR [rbp-72], r9
__sbr_cell_32_135_end:
__sbr_cell_32_136:
    mov QWORD PTR [rbp-80], rsi
__sbr_cell_32_136_end:
__sbr_cell_32_137:
    jae sbr_hf_assemble.La9c2
__sbr_cell_32_137_end:
sbr_hf_assemble.s0:
__sbr_cell_32_138:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_32_138_end:
__sbr_cell_32_139:
    lea rbx, [rax+390848]
__sbr_cell_32_139_end:
__sbr_cell_32_140:
    lea r15, [rax+387776]
__sbr_cell_32_140_end:
__sbr_cell_32_141:
    lea r14d, [rcx+rcx*1+0]
__sbr_cell_32_141_end:
__sbr_cell_32_142:
    lea rax, [rcx+rcx*2+0]
__sbr_cell_32_142_end:
__sbr_cell_32_143:
    shl eax, 7
__sbr_cell_32_143_end:
__sbr_cell_32_144:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_144_end:
__sbr_cell_32_145:
    shl ecx, 6
__sbr_cell_32_145_end:
__sbr_cell_32_146:
    add rcx, rax
__sbr_cell_32_146_end:
__sbr_cell_32_147:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_147_end:
__sbr_cell_32_148:
    add r12, 78000
__sbr_cell_32_148_end:
__sbr_cell_32_149:
    .nops 1
__sbr_cell_32_149_end:
sbr_hf_assemble.La970:
__sbr_cell_32_150:
    lea rdi, [r12-8064]
__sbr_cell_32_150_end:
__sbr_cell_32_151:
    mov rsi, rbx
__sbr_cell_32_151_end:
__sbr_cell_32_152:
    mov rdx, r13
__sbr_cell_32_152_end:
__sbr_cell_32_153:
    vzeroupper
__sbr_cell_32_153_end:
__sbr_cell_32_154:
    call memcpy
__sbr_cell_32_154_end:
sbr_hf_assemble.c0:
__sbr_cell_32_155:
    mov rdi, r12
__sbr_cell_32_155_end:
__sbr_cell_32_156:
    mov rsi, r15
__sbr_cell_32_156_end:
__sbr_cell_32_157:
    mov rdx, r13
__sbr_cell_32_157_end:
__sbr_cell_32_158:
    call memcpy
__sbr_cell_32_158_end:
sbr_hf_assemble.d0:
__sbr_cell_32_159:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_159_end:
__sbr_cell_32_160:
    inc r14
__sbr_cell_32_160_end:
__sbr_cell_32_161:
    movzx eax, BYTE PTR [r8+88733]
__sbr_cell_32_161_end:
__sbr_cell_32_162:
    lea ecx, [rax+rax*1+0]
__sbr_cell_32_162_end:
__sbr_cell_32_163:
    add r12, 192
__sbr_cell_32_163_end:
__sbr_cell_32_164:
    cmp r14, rcx
__sbr_cell_32_164_end:
__sbr_cell_32_165:
    jb sbr_hf_assemble.La970
__sbr_cell_32_165_end:
sbr_hf_assemble.x0:
__sbr_cell_32_166:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_166_end:
__sbr_cell_32_167:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_167_end:
__sbr_cell_32_168:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_168_end:
__sbr_cell_32_169:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_169_end:
sbr_hf_assemble.La9c2:
__sbr_cell_32_170:
    cmp edx, 1
__sbr_cell_32_170_end:
__sbr_cell_32_171:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_171_end:
__sbr_cell_32_172:
    movzx ecx, BYTE PTR [r8+88734]
__sbr_cell_32_172_end:
__sbr_cell_32_173:
    cmp al, cl
__sbr_cell_32_173_end:
__sbr_cell_32_174:
    jae sbr_hf_assemble.Laa62
__sbr_cell_32_174_end:
sbr_hf_assemble.s1:
__sbr_cell_32_175:
    mov rcx, QWORD PTR [rbp-64]
__sbr_cell_32_175_end:
__sbr_cell_32_176:
    lea rbx, [rcx+391040]
__sbr_cell_32_176_end:
__sbr_cell_32_177:
    lea r15, [rcx+387968]
__sbr_cell_32_177_end:
__sbr_cell_32_178:
    movzx r14d, al
__sbr_cell_32_178_end:
__sbr_cell_32_179:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_179_end:
__sbr_cell_32_180:
    add r14d, r14d
__sbr_cell_32_180_end:
__sbr_cell_32_181:
    shl eax, 7
__sbr_cell_32_181_end:
__sbr_cell_32_182:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_182_end:
__sbr_cell_32_183:
    shl ecx, 6
__sbr_cell_32_183_end:
__sbr_cell_32_184:
    add rcx, rax
__sbr_cell_32_184_end:
__sbr_cell_32_185:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_185_end:
__sbr_cell_32_186:
    add r12, 78000
__sbr_cell_32_186_end:
sbr_hf_assemble.Laa10:
__sbr_cell_32_187:
    lea rdi, [r12-8064]
__sbr_cell_32_187_end:
__sbr_cell_32_188:
    mov rsi, rbx
__sbr_cell_32_188_end:
__sbr_cell_32_189:
    mov rdx, r13
__sbr_cell_32_189_end:
__sbr_cell_32_190:
    vzeroupper
__sbr_cell_32_190_end:
__sbr_cell_32_191:
    call memcpy
__sbr_cell_32_191_end:
sbr_hf_assemble.c1:
__sbr_cell_32_192:
    mov rdi, r12
__sbr_cell_32_192_end:
__sbr_cell_32_193:
    mov rsi, r15
__sbr_cell_32_193_end:
__sbr_cell_32_194:
    mov rdx, r13
__sbr_cell_32_194_end:
__sbr_cell_32_195:
    call memcpy
__sbr_cell_32_195_end:
sbr_hf_assemble.d1:
__sbr_cell_32_196:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_196_end:
__sbr_cell_32_197:
    inc r14
__sbr_cell_32_197_end:
__sbr_cell_32_198:
    movzx ecx, BYTE PTR [r8+88734]
__sbr_cell_32_198_end:
__sbr_cell_32_199:
    lea eax, [rcx+rcx*1+0]
__sbr_cell_32_199_end:
__sbr_cell_32_200:
    add r12, 192
__sbr_cell_32_200_end:
__sbr_cell_32_201:
    cmp r14, rax
__sbr_cell_32_201_end:
__sbr_cell_32_202:
    jb sbr_hf_assemble.Laa10
__sbr_cell_32_202_end:
sbr_hf_assemble.x1:
__sbr_cell_32_203:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_203_end:
__sbr_cell_32_204:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_204_end:
__sbr_cell_32_205:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_205_end:
__sbr_cell_32_206:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_206_end:
sbr_hf_assemble.Laa62:
__sbr_cell_32_207:
    cmp edx, 2
__sbr_cell_32_207_end:
__sbr_cell_32_208:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_208_end:
__sbr_cell_32_209:
    movzx eax, BYTE PTR [r8+88735]
__sbr_cell_32_209_end:
__sbr_cell_32_210:
    cmp cl, al
__sbr_cell_32_210_end:
__sbr_cell_32_211:
    jae sbr_hf_assemble.Lab02
__sbr_cell_32_211_end:
sbr_hf_assemble.s2:
__sbr_cell_32_212:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_32_212_end:
__sbr_cell_32_213:
    lea rbx, [rax+391232]
__sbr_cell_32_213_end:
__sbr_cell_32_214:
    lea r15, [rax+388160]
__sbr_cell_32_214_end:
__sbr_cell_32_215:
    movzx r14d, cl
__sbr_cell_32_215_end:
__sbr_cell_32_216:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_216_end:
__sbr_cell_32_217:
    add r14d, r14d
__sbr_cell_32_217_end:
__sbr_cell_32_218:
    shl eax, 7
__sbr_cell_32_218_end:
__sbr_cell_32_219:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_219_end:
__sbr_cell_32_220:
    shl ecx, 6
__sbr_cell_32_220_end:
__sbr_cell_32_221:
    add rcx, rax
__sbr_cell_32_221_end:
__sbr_cell_32_222:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_222_end:
__sbr_cell_32_223:
    add r12, 78000
__sbr_cell_32_223_end:
sbr_hf_assemble.Laab0:
__sbr_cell_32_224:
    lea rdi, [r12-8064]
__sbr_cell_32_224_end:
__sbr_cell_32_225:
    mov rsi, rbx
__sbr_cell_32_225_end:
__sbr_cell_32_226:
    mov rdx, r13
__sbr_cell_32_226_end:
__sbr_cell_32_227:
    vzeroupper
__sbr_cell_32_227_end:
__sbr_cell_32_228:
    call memcpy
__sbr_cell_32_228_end:
sbr_hf_assemble.c2:
__sbr_cell_32_229:
    mov rdi, r12
__sbr_cell_32_229_end:
__sbr_cell_32_230:
    mov rsi, r15
__sbr_cell_32_230_end:
__sbr_cell_32_231:
    mov rdx, r13
__sbr_cell_32_231_end:
__sbr_cell_32_232:
    call memcpy
__sbr_cell_32_232_end:
sbr_hf_assemble.d2:
__sbr_cell_32_233:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_233_end:
__sbr_cell_32_234:
    inc r14
__sbr_cell_32_234_end:
__sbr_cell_32_235:
    movzx eax, BYTE PTR [r8+88735]
__sbr_cell_32_235_end:
__sbr_cell_32_236:
    lea ecx, [rax+rax*1+0]
__sbr_cell_32_236_end:
__sbr_cell_32_237:
    add r12, 192
__sbr_cell_32_237_end:
__sbr_cell_32_238:
    cmp r14, rcx
__sbr_cell_32_238_end:
__sbr_cell_32_239:
    jb sbr_hf_assemble.Laab0
__sbr_cell_32_239_end:
sbr_hf_assemble.x2:
__sbr_cell_32_240:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_240_end:
__sbr_cell_32_241:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_241_end:
__sbr_cell_32_242:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_242_end:
__sbr_cell_32_243:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_243_end:
sbr_hf_assemble.Lab02:
__sbr_cell_32_244:
    cmp edx, 3
__sbr_cell_32_244_end:
__sbr_cell_32_245:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_245_end:
__sbr_cell_32_246:
    movzx ecx, BYTE PTR [r8+88736]
__sbr_cell_32_246_end:
__sbr_cell_32_247:
    cmp al, cl
__sbr_cell_32_247_end:
__sbr_cell_32_248:
    jae sbr_hf_assemble.Laba2
__sbr_cell_32_248_end:
sbr_hf_assemble.s3:
__sbr_cell_32_249:
    mov rcx, QWORD PTR [rbp-64]
__sbr_cell_32_249_end:
__sbr_cell_32_250:
    lea rbx, [rcx+391424]
__sbr_cell_32_250_end:
__sbr_cell_32_251:
    lea r15, [rcx+388352]
__sbr_cell_32_251_end:
__sbr_cell_32_252:
    movzx r14d, al
__sbr_cell_32_252_end:
__sbr_cell_32_253:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_253_end:
__sbr_cell_32_254:
    add r14d, r14d
__sbr_cell_32_254_end:
__sbr_cell_32_255:
    shl eax, 7
__sbr_cell_32_255_end:
__sbr_cell_32_256:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_256_end:
__sbr_cell_32_257:
    shl ecx, 6
__sbr_cell_32_257_end:
__sbr_cell_32_258:
    add rcx, rax
__sbr_cell_32_258_end:
__sbr_cell_32_259:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_259_end:
__sbr_cell_32_260:
    add r12, 78000
__sbr_cell_32_260_end:
sbr_hf_assemble.Lab50:
__sbr_cell_32_261:
    lea rdi, [r12-8064]
__sbr_cell_32_261_end:
__sbr_cell_32_262:
    mov rsi, rbx
__sbr_cell_32_262_end:
__sbr_cell_32_263:
    mov rdx, r13
__sbr_cell_32_263_end:
__sbr_cell_32_264:
    vzeroupper
__sbr_cell_32_264_end:
__sbr_cell_32_265:
    call memcpy
__sbr_cell_32_265_end:
sbr_hf_assemble.c3:
__sbr_cell_32_266:
    mov rdi, r12
__sbr_cell_32_266_end:
__sbr_cell_32_267:
    mov rsi, r15
__sbr_cell_32_267_end:
__sbr_cell_32_268:
    mov rdx, r13
__sbr_cell_32_268_end:
__sbr_cell_32_269:
    call memcpy
__sbr_cell_32_269_end:
sbr_hf_assemble.d3:
__sbr_cell_32_270:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_270_end:
__sbr_cell_32_271:
    inc r14
__sbr_cell_32_271_end:
__sbr_cell_32_272:
    movzx ecx, BYTE PTR [r8+88736]
__sbr_cell_32_272_end:
__sbr_cell_32_273:
    lea eax, [rcx+rcx*1+0]
__sbr_cell_32_273_end:
__sbr_cell_32_274:
    add r12, 192
__sbr_cell_32_274_end:
__sbr_cell_32_275:
    cmp r14, rax
__sbr_cell_32_275_end:
__sbr_cell_32_276:
    jb sbr_hf_assemble.Lab50
__sbr_cell_32_276_end:
sbr_hf_assemble.x3:
__sbr_cell_32_277:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_277_end:
__sbr_cell_32_278:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_278_end:
__sbr_cell_32_279:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_279_end:
__sbr_cell_32_280:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_280_end:
sbr_hf_assemble.Laba2:
__sbr_cell_32_281:
    cmp edx, 4
__sbr_cell_32_281_end:
__sbr_cell_32_282:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_282_end:
__sbr_cell_32_283:
    movzx eax, BYTE PTR [r8+88737]
__sbr_cell_32_283_end:
__sbr_cell_32_284:
    cmp cl, al
__sbr_cell_32_284_end:
__sbr_cell_32_285:
    jae sbr_hf_assemble.Lac42
__sbr_cell_32_285_end:
sbr_hf_assemble.s4:
__sbr_cell_32_286:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_32_286_end:
__sbr_cell_32_287:
    lea rbx, [rax+391616]
__sbr_cell_32_287_end:
__sbr_cell_32_288:
    lea r15, [rax+388544]
__sbr_cell_32_288_end:
__sbr_cell_32_289:
    movzx r14d, cl
__sbr_cell_32_289_end:
__sbr_cell_32_290:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_290_end:
__sbr_cell_32_291:
    add r14d, r14d
__sbr_cell_32_291_end:
__sbr_cell_32_292:
    shl eax, 7
__sbr_cell_32_292_end:
__sbr_cell_32_293:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_293_end:
__sbr_cell_32_294:
    shl ecx, 6
__sbr_cell_32_294_end:
__sbr_cell_32_295:
    add rcx, rax
__sbr_cell_32_295_end:
__sbr_cell_32_296:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_296_end:
__sbr_cell_32_297:
    add r12, 78000
__sbr_cell_32_297_end:
sbr_hf_assemble.Labf0:
__sbr_cell_32_298:
    lea rdi, [r12-8064]
__sbr_cell_32_298_end:
__sbr_cell_32_299:
    mov rsi, rbx
__sbr_cell_32_299_end:
__sbr_cell_32_300:
    mov rdx, r13
__sbr_cell_32_300_end:
__sbr_cell_32_301:
    vzeroupper
__sbr_cell_32_301_end:
__sbr_cell_32_302:
    call memcpy
__sbr_cell_32_302_end:
sbr_hf_assemble.c4:
__sbr_cell_32_303:
    mov rdi, r12
__sbr_cell_32_303_end:
__sbr_cell_32_304:
    mov rsi, r15
__sbr_cell_32_304_end:
__sbr_cell_32_305:
    mov rdx, r13
__sbr_cell_32_305_end:
__sbr_cell_32_306:
    call memcpy
__sbr_cell_32_306_end:
sbr_hf_assemble.d4:
__sbr_cell_32_307:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_307_end:
__sbr_cell_32_308:
    inc r14
__sbr_cell_32_308_end:
__sbr_cell_32_309:
    movzx eax, BYTE PTR [r8+88737]
__sbr_cell_32_309_end:
__sbr_cell_32_310:
    lea ecx, [rax+rax*1+0]
__sbr_cell_32_310_end:
__sbr_cell_32_311:
    add r12, 192
__sbr_cell_32_311_end:
__sbr_cell_32_312:
    cmp r14, rcx
__sbr_cell_32_312_end:
__sbr_cell_32_313:
    jb sbr_hf_assemble.Labf0
__sbr_cell_32_313_end:
sbr_hf_assemble.x4:
__sbr_cell_32_314:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_314_end:
__sbr_cell_32_315:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_315_end:
__sbr_cell_32_316:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_316_end:
__sbr_cell_32_317:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_317_end:
sbr_hf_assemble.Lac42:
__sbr_cell_32_318:
    cmp edx, 5
__sbr_cell_32_318_end:
__sbr_cell_32_319:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_319_end:
__sbr_cell_32_320:
    movzx ecx, BYTE PTR [r8+88738]
__sbr_cell_32_320_end:
__sbr_cell_32_321:
    cmp al, cl
__sbr_cell_32_321_end:
__sbr_cell_32_322:
    jae sbr_hf_assemble.Lace2
__sbr_cell_32_322_end:
sbr_hf_assemble.s5:
__sbr_cell_32_323:
    mov rcx, QWORD PTR [rbp-64]
__sbr_cell_32_323_end:
__sbr_cell_32_324:
    lea rbx, [rcx+391808]
__sbr_cell_32_324_end:
__sbr_cell_32_325:
    lea r15, [rcx+388736]
__sbr_cell_32_325_end:
__sbr_cell_32_326:
    movzx r14d, al
__sbr_cell_32_326_end:
__sbr_cell_32_327:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_327_end:
__sbr_cell_32_328:
    add r14d, r14d
__sbr_cell_32_328_end:
__sbr_cell_32_329:
    shl eax, 7
__sbr_cell_32_329_end:
__sbr_cell_32_330:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_330_end:
__sbr_cell_32_331:
    shl ecx, 6
__sbr_cell_32_331_end:
__sbr_cell_32_332:
    add rcx, rax
__sbr_cell_32_332_end:
__sbr_cell_32_333:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_333_end:
__sbr_cell_32_334:
    add r12, 78000
__sbr_cell_32_334_end:
sbr_hf_assemble.Lac90:
__sbr_cell_32_335:
    lea rdi, [r12-8064]
__sbr_cell_32_335_end:
__sbr_cell_32_336:
    mov rsi, rbx
__sbr_cell_32_336_end:
__sbr_cell_32_337:
    mov rdx, r13
__sbr_cell_32_337_end:
__sbr_cell_32_338:
    vzeroupper
__sbr_cell_32_338_end:
__sbr_cell_32_339:
    call memcpy
__sbr_cell_32_339_end:
sbr_hf_assemble.c5:
__sbr_cell_32_340:
    mov rdi, r12
__sbr_cell_32_340_end:
__sbr_cell_32_341:
    mov rsi, r15
__sbr_cell_32_341_end:
__sbr_cell_32_342:
    mov rdx, r13
__sbr_cell_32_342_end:
__sbr_cell_32_343:
    call memcpy
__sbr_cell_32_343_end:
sbr_hf_assemble.d5:
__sbr_cell_32_344:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_344_end:
__sbr_cell_32_345:
    inc r14
__sbr_cell_32_345_end:
__sbr_cell_32_346:
    movzx ecx, BYTE PTR [r8+88738]
__sbr_cell_32_346_end:
__sbr_cell_32_347:
    lea eax, [rcx+rcx*1+0]
__sbr_cell_32_347_end:
__sbr_cell_32_348:
    add r12, 192
__sbr_cell_32_348_end:
__sbr_cell_32_349:
    cmp r14, rax
__sbr_cell_32_349_end:
__sbr_cell_32_350:
    jb sbr_hf_assemble.Lac90
__sbr_cell_32_350_end:
sbr_hf_assemble.x5:
__sbr_cell_32_351:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_351_end:
__sbr_cell_32_352:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_352_end:
__sbr_cell_32_353:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_353_end:
__sbr_cell_32_354:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_354_end:
sbr_hf_assemble.Lace2:
__sbr_cell_32_355:
    cmp edx, 6
__sbr_cell_32_355_end:
__sbr_cell_32_356:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_356_end:
__sbr_cell_32_357:
    movzx eax, BYTE PTR [r8+88739]
__sbr_cell_32_357_end:
__sbr_cell_32_358:
    cmp cl, al
__sbr_cell_32_358_end:
__sbr_cell_32_359:
    jae sbr_hf_assemble.Lad82
__sbr_cell_32_359_end:
sbr_hf_assemble.s6:
__sbr_cell_32_360:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_32_360_end:
__sbr_cell_32_361:
    lea rbx, [rax+392000]
__sbr_cell_32_361_end:
__sbr_cell_32_362:
    lea r15, [rax+388928]
__sbr_cell_32_362_end:
__sbr_cell_32_363:
    movzx r14d, cl
__sbr_cell_32_363_end:
__sbr_cell_32_364:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_364_end:
__sbr_cell_32_365:
    add r14d, r14d
__sbr_cell_32_365_end:
__sbr_cell_32_366:
    shl eax, 7
__sbr_cell_32_366_end:
__sbr_cell_32_367:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_367_end:
__sbr_cell_32_368:
    shl ecx, 6
__sbr_cell_32_368_end:
__sbr_cell_32_369:
    add rcx, rax
__sbr_cell_32_369_end:
__sbr_cell_32_370:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_370_end:
__sbr_cell_32_371:
    add r12, 78000
__sbr_cell_32_371_end:
sbr_hf_assemble.Lad30:
__sbr_cell_32_372:
    lea rdi, [r12-8064]
__sbr_cell_32_372_end:
__sbr_cell_32_373:
    mov rsi, rbx
__sbr_cell_32_373_end:
__sbr_cell_32_374:
    mov rdx, r13
__sbr_cell_32_374_end:
__sbr_cell_32_375:
    vzeroupper
__sbr_cell_32_375_end:
__sbr_cell_32_376:
    call memcpy
__sbr_cell_32_376_end:
sbr_hf_assemble.c6:
__sbr_cell_32_377:
    mov rdi, r12
__sbr_cell_32_377_end:
__sbr_cell_32_378:
    mov rsi, r15
__sbr_cell_32_378_end:
__sbr_cell_32_379:
    mov rdx, r13
__sbr_cell_32_379_end:
__sbr_cell_32_380:
    call memcpy
__sbr_cell_32_380_end:
sbr_hf_assemble.d6:
__sbr_cell_32_381:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_381_end:
__sbr_cell_32_382:
    inc r14
__sbr_cell_32_382_end:
__sbr_cell_32_383:
    movzx eax, BYTE PTR [r8+88739]
__sbr_cell_32_383_end:
__sbr_cell_32_384:
    lea ecx, [rax+rax*1+0]
__sbr_cell_32_384_end:
__sbr_cell_32_385:
    add r12, 192
__sbr_cell_32_385_end:
__sbr_cell_32_386:
    cmp r14, rcx
__sbr_cell_32_386_end:
__sbr_cell_32_387:
    jb sbr_hf_assemble.Lad30
__sbr_cell_32_387_end:
sbr_hf_assemble.x6:
__sbr_cell_32_388:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_388_end:
__sbr_cell_32_389:
    mov edx, DWORD PTR [rbp-56]
__sbr_cell_32_389_end:
__sbr_cell_32_390:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_390_end:
__sbr_cell_32_391:
    mov rsi, QWORD PTR [rbp-80]
__sbr_cell_32_391_end:
sbr_hf_assemble.Lad82:
__sbr_cell_32_392:
    cmp edx, 7
__sbr_cell_32_392_end:
__sbr_cell_32_393:
    je sbr_hf_assemble.Lae20
__sbr_cell_32_393_end:
__sbr_cell_32_394:
    cmp al, BYTE PTR [r8+88740]
__sbr_cell_32_394_end:
__sbr_cell_32_395:
    jae sbr_hf_assemble.Lae0d
__sbr_cell_32_395_end:
sbr_hf_assemble.s7:
__sbr_cell_32_396:
    mov rbx, r13
__sbr_cell_32_396_end:
__sbr_cell_32_397:
    mov rcx, QWORD PTR [rbp-64]
__sbr_cell_32_397_end:
__sbr_cell_32_398:
    lea r13, [rcx+392192]
__sbr_cell_32_398_end:
__sbr_cell_32_399:
    lea r15, [rcx+389120]
__sbr_cell_32_399_end:
__sbr_cell_32_400:
    movzx r14d, al
__sbr_cell_32_400_end:
__sbr_cell_32_401:
    lea rax, [r14+r14*2+0]
__sbr_cell_32_401_end:
__sbr_cell_32_402:
    add r14d, r14d
__sbr_cell_32_402_end:
__sbr_cell_32_403:
    shl eax, 7
__sbr_cell_32_403_end:
__sbr_cell_32_404:
    lea rcx, [rsi+rsi*2+0]
__sbr_cell_32_404_end:
__sbr_cell_32_405:
    shl ecx, 6
__sbr_cell_32_405_end:
__sbr_cell_32_406:
    add rcx, rax
__sbr_cell_32_406_end:
__sbr_cell_32_407:
    lea r12, [r8+rcx*1+0]
__sbr_cell_32_407_end:
__sbr_cell_32_408:
    add r12, 78000
__sbr_cell_32_408_end:
sbr_hf_assemble.Ladcc:
__sbr_cell_32_409:
    lea rdi, [r12-8064]
__sbr_cell_32_409_end:
__sbr_cell_32_410:
    mov rsi, r13
__sbr_cell_32_410_end:
__sbr_cell_32_411:
    mov rdx, rbx
__sbr_cell_32_411_end:
__sbr_cell_32_412:
    vzeroupper
__sbr_cell_32_412_end:
__sbr_cell_32_413:
    call memcpy
__sbr_cell_32_413_end:
sbr_hf_assemble.c7:
__sbr_cell_32_414:
    mov rdi, r12
__sbr_cell_32_414_end:
__sbr_cell_32_415:
    mov rsi, r15
__sbr_cell_32_415_end:
__sbr_cell_32_416:
    mov rdx, rbx
__sbr_cell_32_416_end:
__sbr_cell_32_417:
    call memcpy
__sbr_cell_32_417_end:
sbr_hf_assemble.d7:
__sbr_cell_32_418:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_418_end:
__sbr_cell_32_419:
    inc r14
__sbr_cell_32_419_end:
__sbr_cell_32_420:
    movzx eax, BYTE PTR [r8+88740]
__sbr_cell_32_420_end:
__sbr_cell_32_421:
    add eax, eax
__sbr_cell_32_421_end:
__sbr_cell_32_422:
    add r12, 192
__sbr_cell_32_422_end:
__sbr_cell_32_423:
    cmp r14, rax
__sbr_cell_32_423_end:
__sbr_cell_32_424:
    jb sbr_hf_assemble.Ladcc
__sbr_cell_32_424_end:
sbr_hf_assemble.Lae0d:
__sbr_cell_32_425:
    cmp DWORD PTR [rbp-56], 8
__sbr_cell_32_425_end:
__sbr_cell_32_426:
    vmovdqa xmm4, XMMWORD PTR [rbp-112]
__sbr_cell_32_426_end:
__sbr_cell_32_427:
    mov r9, QWORD PTR [rbp-72]
__sbr_cell_32_427_end:
__sbr_cell_32_428:
    jne sbr_hf_assemble.Lb84d
__sbr_cell_32_428_end:
sbr_hf_assemble.Lae20:
__sbr_cell_32_429:
    mov rsi, QWORD PTR [rbp-120]
__sbr_cell_32_429_end:
__sbr_cell_32_430:
    mov ecx, esi
__sbr_cell_32_430_end:
__sbr_cell_32_431:
    mov rdx, QWORD PTR [rbp-136]
__sbr_cell_32_431_end:
__sbr_cell_32_432:
    mov rdi, QWORD PTR [rbp-128]
__sbr_cell_32_432_end:
__sbr_cell_32_433:
    lea rax, [rdi+rdx*8+0]
__sbr_cell_32_433_end:
__sbr_cell_32_434:
    mov QWORD PTR [rbp-80], rax
__sbr_cell_32_434_end:
__sbr_cell_32_435:
    lea rax, [rdx+rdx*4+0]
__sbr_cell_32_435_end:
__sbr_cell_32_436:
    shl rax, 6
__sbr_cell_32_436_end:
__sbr_cell_32_437:
    add QWORD PTR [rbp-192], rax
__sbr_cell_32_437_end:
sbr_hf_assemble.m1:
__sbr_cell_32_438:
    mov r10, QWORD PTR [rbp-64]
__sbr_cell_32_438_end:
__sbr_cell_32_439:
    lea rax, [r10+389312]
__sbr_cell_32_439_end:
__sbr_cell_32_440:
    mov QWORD PTR [rbp-232], rax
__sbr_cell_32_440_end:
__sbr_cell_32_441:
    mov eax, edx
__sbr_cell_32_441_end:
__sbr_cell_32_442:
    and eax, 1
__sbr_cell_32_442_end:
__sbr_cell_32_443:
    mov DWORD PTR [rbp-156], eax
__sbr_cell_32_443_end:
__sbr_cell_32_444:
    shl r9d, 6
__sbr_cell_32_444_end:
__sbr_cell_32_445:
    lea rax, [r9+r9*2+0]
__sbr_cell_32_445_end:
__sbr_cell_32_446:
    add QWORD PTR [rbp-152], rax
__sbr_cell_32_446_end:
__sbr_cell_32_447:
    lea r9, [rcx-1]
__sbr_cell_32_447_end:
__sbr_cell_32_448:
    vbroadcastss xmm0, DWORD PTR [rip+LCPI17_12]
__sbr_cell_32_448_end:
__sbr_cell_32_449:
    vpinsrd xmm0, xmm0, esi, 0
__sbr_cell_32_449_end:
__sbr_cell_32_450:
    vmovdqa XMMWORD PTR [rbp-256], xmm0
__sbr_cell_32_450_end:
sbr_hf_assemble.m2:
__sbr_cell_32_451:
    mov esi, ecx
__sbr_cell_32_451_end:
__sbr_cell_32_452:
    and esi, 2147483644
__sbr_cell_32_452_end:
__sbr_cell_32_453:
    mov QWORD PTR [rbp-208], rsi
__sbr_cell_32_453_end:
__sbr_cell_32_454:
    mov esi, ecx
__sbr_cell_32_454_end:
__sbr_cell_32_455:
    shr esi, 2
__sbr_cell_32_455_end:
__sbr_cell_32_456:
    and esi, 536870911
__sbr_cell_32_456_end:
__sbr_cell_32_457:
    shl rsi, 4
__sbr_cell_32_457_end:
__sbr_cell_32_458:
    mov QWORD PTR [rbp-200], rsi
__sbr_cell_32_458_end:
__sbr_cell_32_459:
    add rax, r8
__sbr_cell_32_459_end:
__sbr_cell_32_460:
    add rax, 78000
__sbr_cell_32_460_end:
__sbr_cell_32_461:
    mov QWORD PTR [rbp-224], rax
__sbr_cell_32_461_end:
__sbr_cell_32_462:
    lea rax, [rdi+rdx*8+0]
__sbr_cell_32_462_end:
__sbr_cell_32_463:
    add rax, 8
__sbr_cell_32_463_end:
__sbr_cell_32_464:
    mov QWORD PTR [rbp-216], rax
__sbr_cell_32_464_end:
__sbr_cell_32_465:
    lea r14, [r10+389316]
__sbr_cell_32_465_end:
__sbr_cell_32_466:
    xor r10d, r10d
__sbr_cell_32_466_end:
sbr_hf_assemble.m3:
__sbr_cell_32_467:
    vmovss xmm5, DWORD PTR [rip+LCPI17_6]
__sbr_cell_32_467_end:
__sbr_cell_32_468:
    vmovss xmm6, DWORD PTR [rip+LCPI17_7]
__sbr_cell_32_468_end:
__sbr_cell_32_469:
    vmovss xmm7, DWORD PTR [rip+LCPI17_8]
__sbr_cell_32_469_end:
__sbr_cell_32_470:
    vmovss xmm8, DWORD PTR [rip+LCPI17_9]
__sbr_cell_32_470_end:
__sbr_cell_32_471:
    vmovss xmm9, DWORD PTR [rip+LCPI17_10]
__sbr_cell_32_471_end:
__sbr_cell_32_472:
    vbroadcastss xmm10, DWORD PTR [rip+LCPI17_6]
__sbr_cell_32_472_end:
__sbr_cell_32_473:
    vbroadcastss xmm11, DWORD PTR [rip+LCPI17_7]
__sbr_cell_32_473_end:
__sbr_cell_32_474:
    vbroadcastss xmm12, DWORD PTR [rip+LCPI17_8]
__sbr_cell_32_474_end:
__sbr_cell_32_475:
    vbroadcastss xmm13, DWORD PTR [rip+LCPI17_9]
__sbr_cell_32_475_end:
__sbr_cell_32_476:
    vbroadcastss xmm14, DWORD PTR [rip+LCPI17_10]
__sbr_cell_32_476_end:
__sbr_cell_32_477:
    mov QWORD PTR [rbp-184], rcx
__sbr_cell_32_477_end:
__sbr_cell_32_478:
    mov QWORD PTR [rbp-240], r9
__sbr_cell_32_478_end:
sbr_hf_assemble.Laf40:
__sbr_cell_32_479:
    movzx r11d, BYTE PTR [r8+r10*1+88732]
__sbr_cell_32_479_end:
__sbr_cell_32_480:
    lea rdi, [r10+1]
__sbr_cell_32_480_end:
__sbr_cell_32_481:
    cmp r11b, BYTE PTR [r8+r10*1+88733]
__sbr_cell_32_481_end:
__sbr_cell_32_482:
    jae sbr_hf_assemble.Lb400
__sbr_cell_32_482_end:
__sbr_cell_32_483:
    lea rax, [r10+r10*2+0]
__sbr_cell_32_483_end:
__sbr_cell_32_484:
    shl rax, 6
__sbr_cell_32_484_end:
__sbr_cell_32_485:
    add rax, QWORD PTR [rbp-232]
__sbr_cell_32_485_end:
__sbr_cell_32_486:
    mov QWORD PTR [rbp-168], rax
__sbr_cell_32_486_end:
__sbr_cell_32_487:
    lea r15d, [r11+r11*1+0]
__sbr_cell_32_487_end:
__sbr_cell_32_488:
    lea r12, [r11+r11*2+0]
__sbr_cell_32_488_end:
__sbr_cell_32_489:
    shl r12d, 7
__sbr_cell_32_489_end:
__sbr_cell_32_490:
    add r12, QWORD PTR [rbp-224]
__sbr_cell_32_490_end:
__sbr_cell_32_491:
    shl r11d, 10
__sbr_cell_32_491_end:
__sbr_cell_32_492:
    add r11, QWORD PTR [rbp-216]
__sbr_cell_32_492_end:
__sbr_cell_32_493:
    mov QWORD PTR [rbp-72], rdi
__sbr_cell_32_493_end:
__sbr_cell_32_494:
    jmp sbr_hf_assemble.Lafd9
__sbr_cell_32_494_end:
__sbr_cell_32_495:
    .nops 1
__sbr_cell_32_495_end:
sbr_hf_assemble.Lafa0:
__sbr_cell_32_496:
    vpaddd xmm0, xmm3, XMMWORD PTR [rbp-256]
__sbr_cell_32_496_end:
__sbr_cell_32_497:
    vpand xmm4, xmm0, XMMWORD PTR [rip+LCPI17_11]
__sbr_cell_32_497_end:
__sbr_cell_32_498:
    inc r15
__sbr_cell_32_498_end:
__sbr_cell_32_499:
    mov rdi, QWORD PTR [rbp-72]
__sbr_cell_32_499_end:
__sbr_cell_32_500:
    movzx eax, BYTE PTR [r8+rdi*1+88732]
__sbr_cell_32_500_end:
__sbr_cell_32_501:
    add eax, eax
__sbr_cell_32_501_end:
__sbr_cell_32_502:
    add r12, 192
__sbr_cell_32_502_end:
__sbr_cell_32_503:
    add r11, 512
__sbr_cell_32_503_end:
__sbr_cell_32_504:
    cmp r15, rax
__sbr_cell_32_504_end:
__sbr_cell_32_505:
    jae sbr_hf_assemble.Lb400
__sbr_cell_32_505_end:
sbr_hf_assemble.Lafd9:
__sbr_cell_32_506:
    cmp DWORD PTR [rbp-84], 0
__sbr_cell_32_506_end:
__sbr_cell_32_507:
    jne sbr_hf_assemble.Lb000
__sbr_cell_32_507_end:
__sbr_cell_32_508:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_32_508_end:
__sbr_cell_32_509:
    mov eax, DWORD PTR [rax+0]
__sbr_cell_32_509_end:
__sbr_cell_32_510:
    cmp r10, rax
__sbr_cell_32_510_end:
__sbr_cell_32_511:
    je sbr_hf_assemble.Lb000
__sbr_cell_32_511_end:
__sbr_cell_32_512:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_32_512_end:
__sbr_cell_32_513:
    mov eax, DWORD PTR [rax+4]
__sbr_cell_32_513_end:
__sbr_cell_32_514:
    cmp r10, rax
__sbr_cell_32_514_end:
__sbr_cell_32_515:
    jne sbr_hf_assemble.Lb248
__sbr_cell_32_515_end:
sbr_hf_assemble.Lb000:
__sbr_cell_32_516:
    mov rax, r15
__sbr_cell_32_516_end:
__sbr_cell_32_517:
    shl rax, 6
__sbr_cell_32_517_end:
__sbr_cell_32_518:
    lea r13, [rax+rax*2+0]
__sbr_cell_32_518_end:
__sbr_cell_32_519:
    mov rax, QWORD PTR [rbp-152]
__sbr_cell_32_519_end:
__sbr_cell_32_520:
    lea rdx, [rax+r13*1+0]
__sbr_cell_32_520_end:
__sbr_cell_32_521:
    add r13, QWORD PTR [rbp-176]
__sbr_cell_32_521_end:
sbr_hf_assemble.Lb01d:
__sbr_cell_32_522:
    cmp DWORD PTR [rbp-136], 65
__sbr_cell_32_522_end:
__sbr_cell_32_523:
    jae sbr_hf_assemble.Lb83e
__sbr_cell_32_523_end:
__sbr_cell_32_524:
    mov QWORD PTR [rbp-128], r11
__sbr_cell_32_524_end:
__sbr_cell_32_525:
    mov rbx, r15
__sbr_cell_32_525_end:
__sbr_cell_32_526:
    shl rbx, 9
__sbr_cell_32_526_end:
__sbr_cell_32_527:
    add rbx, QWORD PTR [rbp-80]
__sbr_cell_32_527_end:
__sbr_cell_32_528:
    mov QWORD PTR [rbp-56], r15
__sbr_cell_32_528_end:
__sbr_cell_32_529:
    lea r8, [r15+2]
__sbr_cell_32_529_end:
__sbr_cell_32_530:
    mov rdi, rbx
__sbr_cell_32_530_end:
__sbr_cell_32_531:
    mov rsi, QWORD PTR [rbp-192]
__sbr_cell_32_531_end:
__sbr_cell_32_532:
    mov rax, QWORD PTR [rbp-64]
__sbr_cell_32_532_end:
__sbr_cell_32_533:
    vmovdqa XMMWORD PTR [rbp-112], xmm4
__sbr_cell_32_533_end:
__sbr_cell_32_534:
    mov r15, r10
__sbr_cell_32_534_end:
__sbr_cell_32_535:
    vzeroupper
__sbr_cell_32_535_end:
__sbr_cell_32_536:
    call QWORD PTR [rax+393768]
__sbr_cell_32_536_end:
sbr_hf_assemble.g1:
__sbr_cell_32_537:
    mov r10, r15
__sbr_cell_32_537_end:
__sbr_cell_32_538:
    vmovdqa xmm3, XMMWORD PTR [rbp-112]
__sbr_cell_32_538_end:
__sbr_cell_32_539:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_32_539_end:
__sbr_cell_32_540:
    mov eax, DWORD PTR [rax+0]
__sbr_cell_32_540_end:
__sbr_cell_32_541:
    vpextrd ecx, xmm3, 1
__sbr_cell_32_541_end:
__sbr_cell_32_542:
    cmp r15, rax
__sbr_cell_32_542_end:
__sbr_cell_32_543:
    je sbr_hf_assemble.Lb08f
__sbr_cell_32_543_end:
__sbr_cell_32_544:
    mov rax, QWORD PTR [rbp-144]
__sbr_cell_32_544_end:
__sbr_cell_32_545:
    mov eax, DWORD PTR [rax+4]
__sbr_cell_32_545_end:
__sbr_cell_32_546:
    cmp r10, rax
__sbr_cell_32_546_end:
__sbr_cell_32_547:
    jne sbr_hf_assemble.Lb1a0
__sbr_cell_32_547_end:
sbr_hf_assemble.Lb08f:
__sbr_cell_32_548:
    cmp DWORD PTR [rbp-136], 64
__sbr_cell_32_548_end:
__sbr_cell_32_549:
    je sbr_hf_assemble.Lb843
__sbr_cell_32_549_end:
__sbr_cell_32_550:
    mov esi, ecx
__sbr_cell_32_550_end:
__sbr_cell_32_551:
    and esi, 1
__sbr_cell_32_551_end:
__sbr_cell_32_552:
    add ecx, DWORD PTR [rbp-156]
__sbr_cell_32_552_end:
__sbr_cell_32_553:
    and ecx, 2
__sbr_cell_32_553_end:
__sbr_cell_32_554:
    mov eax, 1
__sbr_cell_32_554_end:
__sbr_cell_32_555:
    sub eax, ecx
__sbr_cell_32_555_end:
__sbr_cell_32_556:
    xor edi, edi
__sbr_cell_32_556_end:
__sbr_cell_32_557:
    mov edx, esi
__sbr_cell_32_557_end:
__sbr_cell_32_558:
    mov rcx, QWORD PTR [rbp-184]
__sbr_cell_32_558_end:
__sbr_cell_32_559:
    cmp ecx, 2
__sbr_cell_32_559_end:
__sbr_cell_32_560:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_560_end:
__sbr_cell_32_561:
    mov r9, QWORD PTR [rbp-240]
__sbr_cell_32_561_end:
__sbr_cell_32_562:
    vmovss xmm5, DWORD PTR [rip+LCPI17_6]
__sbr_cell_32_562_end:
__sbr_cell_32_563:
    vmovss xmm6, DWORD PTR [rip+LCPI17_7]
__sbr_cell_32_563_end:
__sbr_cell_32_564:
    vmovss xmm7, DWORD PTR [rip+LCPI17_8]
__sbr_cell_32_564_end:
__sbr_cell_32_565:
    vmovss xmm8, DWORD PTR [rip+LCPI17_9]
__sbr_cell_32_565_end:
__sbr_cell_32_566:
    vmovss xmm9, DWORD PTR [rip+LCPI17_10]
__sbr_cell_32_566_end:
__sbr_cell_32_567:
    vbroadcastss xmm10, DWORD PTR [rip+LCPI17_6]
__sbr_cell_32_567_end:
__sbr_cell_32_568:
    vbroadcastss xmm11, DWORD PTR [rip+LCPI17_7]
__sbr_cell_32_568_end:
__sbr_cell_32_569:
    vbroadcastss xmm12, DWORD PTR [rip+LCPI17_8]
__sbr_cell_32_569_end:
__sbr_cell_32_570:
    vbroadcastss xmm13, DWORD PTR [rip+LCPI17_9]
__sbr_cell_32_570_end:
__sbr_cell_32_571:
    vbroadcastss xmm14, DWORD PTR [rip+LCPI17_10]
__sbr_cell_32_571_end:
__sbr_cell_32_572:
    mov r11, QWORD PTR [rbp-128]
__sbr_cell_32_572_end:
__sbr_cell_32_573:
    mov r15, QWORD PTR [rbp-56]
__sbr_cell_32_573_end:
__sbr_cell_32_574:
    jl sbr_hf_assemble.Lb16c
__sbr_cell_32_574_end:
sbr_hf_assemble.n2:
__sbr_cell_32_575:
    mov edi, esi
__sbr_cell_32_575_end:
__sbr_cell_32_576:
    neg edi
__sbr_cell_32_576_end:
__sbr_cell_32_577:
    xor edi, eax
__sbr_cell_32_577_end:
__sbr_cell_32_578:
    add edi, esi
__sbr_cell_32_578_end:
__sbr_cell_32_579:
    vcvtsi2ss xmm0, xmm15, eax
__sbr_cell_32_579_end:
__sbr_cell_32_580:
    vcvtsi2ss xmm1, xmm15, edi
__sbr_cell_32_580_end:
__sbr_cell_32_581:
    lea rsi, [r11+rdx*4+0]
__sbr_cell_32_581_end:
__sbr_cell_32_582:
    xor edi, edi
__sbr_cell_32_582_end:
__sbr_cell_32_583:
    .nops 1
__sbr_cell_32_583_end:
sbr_hf_assemble.Lb140:
__sbr_cell_32_584:
    vmulss xmm2, xmm0, DWORD PTR [r14+rdi*4-4]
__sbr_cell_32_584_end:
__sbr_cell_32_585:
    vaddss xmm2, xmm2, DWORD PTR [rsi+rdi*8-8]
__sbr_cell_32_585_end:
__sbr_cell_32_586:
    vmovss DWORD PTR [rsi+rdi*8-8], xmm2
__sbr_cell_32_586_end:
__sbr_cell_32_587:
    vmulss xmm2, xmm1, DWORD PTR [r14+rdi*4+0]
__sbr_cell_32_587_end:
__sbr_cell_32_588:
    vaddss xmm2, xmm2, DWORD PTR [rsi+rdi*8+0]
__sbr_cell_32_588_end:
__sbr_cell_32_589:
    vmovss DWORD PTR [rsi+rdi*8+0], xmm2
__sbr_cell_32_589_end:
__sbr_cell_32_590:
    add rdi, 2
__sbr_cell_32_590_end:
__sbr_cell_32_591:
    cmp rdi, r9
__sbr_cell_32_591_end:
__sbr_cell_32_592:
    jl sbr_hf_assemble.Lb140
__sbr_cell_32_592_end:
sbr_hf_assemble.Lb16c:
__sbr_cell_32_593:
    test cl, 1
__sbr_cell_32_593_end:
__sbr_cell_32_594:
    je sbr_hf_assemble.Lafa0
__sbr_cell_32_594_end:
__sbr_cell_32_595:
    lea rdx, [rbx+rdx*4+0]
__sbr_cell_32_595_end:
__sbr_cell_32_596:
    vcvtsi2ss xmm0, xmm15, eax
__sbr_cell_32_596_end:
__sbr_cell_32_597:
    mov eax, edi
__sbr_cell_32_597_end:
__sbr_cell_32_598:
    mov rsi, QWORD PTR [rbp-168]
__sbr_cell_32_598_end:
__sbr_cell_32_599:
    vmulss xmm0, xmm0, DWORD PTR [rsi+rax*4+0]
__sbr_cell_32_599_end:
__sbr_cell_32_600:
    add edi, edi
__sbr_cell_32_600_end:
__sbr_cell_32_601:
    vaddss xmm0, xmm0, DWORD PTR [rdx+rdi*4+0]
__sbr_cell_32_601_end:
__sbr_cell_32_602:
    vmovss DWORD PTR [rdx+rdi*4+0], xmm0
__sbr_cell_32_602_end:
__sbr_cell_32_603:
    jmp sbr_hf_assemble.Lafa0
__sbr_cell_32_603_end:
__sbr_cell_32_604:
    .nops 1
__sbr_cell_32_604_end:
sbr_hf_assemble.Lb1a0:
__sbr_cell_32_605:
    cmp ecx, 4
__sbr_cell_32_605_end:
__sbr_cell_32_606:
    jae sbr_hf_assemble.Lb848
__sbr_cell_32_606_end:
__sbr_cell_32_607:
    mov eax, ecx
__sbr_cell_32_607_end:
__sbr_cell_32_608:
    vmovd ecx, xmm3
__sbr_cell_32_608_end:
__sbr_cell_32_609:
    mov rdi, rbx
__sbr_cell_32_609_end:
__sbr_cell_32_610:
    mov rsi, QWORD PTR [rbp-168]
__sbr_cell_32_610_end:
__sbr_cell_32_611:
    mov rdx, r13
__sbr_cell_32_611_end:
__sbr_cell_32_612:
    mov r8, QWORD PTR [rbp-136]
__sbr_cell_32_612_end:
__sbr_cell_32_613:
    mov r9, QWORD PTR [rbp-120]
__sbr_cell_32_613_end:
__sbr_cell_32_614:
    mov r10, QWORD PTR [rbp-64]
__sbr_cell_32_614_end:
__sbr_cell_32_615:
    call QWORD PTR [r10+rax*8+393776]
__sbr_cell_32_615_end:
sbr_hf_assemble.a1:
__sbr_cell_32_616:
    vmovdqa xmm3, XMMWORD PTR [rbp-112]
__sbr_cell_32_616_end:
__sbr_cell_32_617:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_32_617_end:
__sbr_cell_32_618:
    mov rcx, QWORD PTR [rbp-184]
__sbr_cell_32_618_end:
__sbr_cell_32_619:
    vmovss xmm5, DWORD PTR [rip+LCPI17_6]
__sbr_cell_32_619_end:
__sbr_cell_32_620:
    vmovss xmm6, DWORD PTR [rip+LCPI17_7]
__sbr_cell_32_620_end:
__sbr_cell_32_621:
    vmovss xmm7, DWORD PTR [rip+LCPI17_8]
__sbr_cell_32_621_end:
__sbr_cell_32_622:
    vmovss xmm8, DWORD PTR [rip+LCPI17_9]
__sbr_cell_32_622_end:
__sbr_cell_32_623:
    vmovss xmm9, DWORD PTR [rip+LCPI17_10]
__sbr_cell_32_623_end:
__sbr_cell_32_624:
    vbroadcastss xmm10, DWORD PTR [rip+LCPI17_6]
__sbr_cell_32_624_end:
__sbr_cell_32_625:
    vbroadcastss xmm11, DWORD PTR [rip+LCPI17_7]
__sbr_cell_32_625_end:
__sbr_cell_32_626:
    vbroadcastss xmm12, DWORD PTR [rip+LCPI17_8]
__sbr_cell_32_626_end:
__sbr_cell_32_627:
    vbroadcastss xmm13, DWORD PTR [rip+LCPI17_9]
__sbr_cell_32_627_end:
__sbr_cell_32_628:
    vbroadcastss xmm14, DWORD PTR [rip+LCPI17_10]
__sbr_cell_32_628_end:
__sbr_cell_32_629:
    mov r10, r15
__sbr_cell_32_629_end:
__sbr_cell_32_630:
    mov r11, QWORD PTR [rbp-128]
__sbr_cell_32_630_end:
__sbr_cell_32_631:
    mov r15, QWORD PTR [rbp-56]
__sbr_cell_32_631_end:
__sbr_cell_32_632:
    jmp sbr_hf_assemble.Lafa0
__sbr_cell_32_632_end:
sbr_hf_assemble.Lb248:
__sbr_cell_32_633:
    lea rdx, [rbp-640]
__sbr_cell_32_633_end:
__sbr_cell_32_634:
    lea r13, [rbp-448]
__sbr_cell_32_634_end:
__sbr_cell_32_635:
    test ecx, ecx
__sbr_cell_32_635_end:
__sbr_cell_32_636:
    jle sbr_hf_assemble.Lb01d
__sbr_cell_32_636_end:
__sbr_cell_32_637:
    cmp DWORD PTR [rbp-120], 4
__sbr_cell_32_637_end:
__sbr_cell_32_638:
    jae sbr_hf_assemble.Lb26b
__sbr_cell_32_638_end:
__sbr_cell_32_639:
    xor eax, eax
__sbr_cell_32_639_end:
__sbr_cell_32_640:
    jmp sbr_hf_assemble.Lb340
__sbr_cell_32_640_end:
sbr_hf_assemble.Lb26b:
__sbr_cell_32_641:
    xor eax, eax
__sbr_cell_32_641_end:
__sbr_cell_32_642:
    mov rdx, QWORD PTR [rbp-200]
__sbr_cell_32_642_end:
__sbr_cell_32_643:
    .nops 1
__sbr_cell_32_643_end:
sbr_hf_assemble.Lb280:
__sbr_cell_32_644:
    vmulps xmm0, xmm10, XMMWORD PTR [r12+rax*1+0]
__sbr_cell_32_644_end:
__sbr_cell_32_645:
    vmulps xmm1, xmm11, XMMWORD PTR [r12+rax*1-192]
__sbr_cell_32_645_end:
__sbr_cell_32_646:
    vmulps xmm2, xmm12, XMMWORD PTR [r12+rax*1-384]
__sbr_cell_32_646_end:
__sbr_cell_32_647:
    vaddps xmm0, xmm0, xmm1
__sbr_cell_32_647_end:
__sbr_cell_32_648:
    vaddps xmm0, xmm0, xmm2
__sbr_cell_32_648_end:
__sbr_cell_32_649:
    vmulps xmm1, xmm10, XMMWORD PTR [r12+rax*1-8064]
__sbr_cell_32_649_end:
__sbr_cell_32_650:
    vmulps xmm2, xmm11, XMMWORD PTR [r12+rax*1-8256]
__sbr_cell_32_650_end:
__sbr_cell_32_651:
    vmulps xmm3, xmm12, XMMWORD PTR [r12+rax*1-8448]
__sbr_cell_32_651_end:
__sbr_cell_32_652:
    vaddps xmm1, xmm1, xmm2
__sbr_cell_32_652_end:
__sbr_cell_32_653:
    vaddps xmm1, xmm1, xmm3
__sbr_cell_32_653_end:
__sbr_cell_32_654:
    vmulps xmm2, xmm13, XMMWORD PTR [r12+rax*1-8640]
__sbr_cell_32_654_end:
__sbr_cell_32_655:
    vaddps xmm1, xmm1, xmm2
__sbr_cell_32_655_end:
sbr_hf_assemble.v1:
__sbr_cell_32_656:
    vmulps xmm2, xmm13, XMMWORD PTR [r12+rax*1-576]
__sbr_cell_32_656_end:
__sbr_cell_32_657:
    vaddps xmm0, xmm0, xmm2
__sbr_cell_32_657_end:
__sbr_cell_32_658:
    vmulps xmm2, xmm14, XMMWORD PTR [r12+rax*1-768]
__sbr_cell_32_658_end:
__sbr_cell_32_659:
    vmulps xmm3, xmm14, XMMWORD PTR [r12+rax*1-8832]
__sbr_cell_32_659_end:
__sbr_cell_32_660:
    vaddps xmm0, xmm0, xmm2
__sbr_cell_32_660_end:
__sbr_cell_32_661:
    vaddps xmm1, xmm1, xmm3
__sbr_cell_32_661_end:
__sbr_cell_32_662:
    vmovaps XMMWORD PTR [rbp+rax*1-640], xmm1
__sbr_cell_32_662_end:
__sbr_cell_32_663:
    vmovaps XMMWORD PTR [rbp+rax*1-448], xmm0
__sbr_cell_32_663_end:
__sbr_cell_32_664:
    add rax, 16
__sbr_cell_32_664_end:
__sbr_cell_32_665:
    cmp rdx, rax
__sbr_cell_32_665_end:
__sbr_cell_32_666:
    jne sbr_hf_assemble.Lb280
__sbr_cell_32_666_end:
sbr_hf_assemble.v2:
__sbr_cell_32_667:
    mov rsi, QWORD PTR [rbp-208]
__sbr_cell_32_667_end:
__sbr_cell_32_668:
    mov rax, rsi
__sbr_cell_32_668_end:
__sbr_cell_32_669:
    lea rdx, [rbp-640]
__sbr_cell_32_669_end:
__sbr_cell_32_670:
    lea r13, [rbp-448]
__sbr_cell_32_670_end:
__sbr_cell_32_671:
    cmp esi, ecx
__sbr_cell_32_671_end:
__sbr_cell_32_672:
    je sbr_hf_assemble.Lb01d
__sbr_cell_32_672_end:
__sbr_cell_32_673:
    .nops 1
__sbr_cell_32_673_end:
sbr_hf_assemble.Lb340:
__sbr_cell_32_674:
    vmulss xmm0, xmm5, DWORD PTR [r12+rax*4+0]
__sbr_cell_32_674_end:
__sbr_cell_32_675:
    vmulss xmm1, xmm6, DWORD PTR [r12+rax*4-192]
__sbr_cell_32_675_end:
__sbr_cell_32_676:
    vmulss xmm2, xmm7, DWORD PTR [r12+rax*4-384]
__sbr_cell_32_676_end:
__sbr_cell_32_677:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_32_677_end:
__sbr_cell_32_678:
    vaddss xmm0, xmm0, xmm2
__sbr_cell_32_678_end:
__sbr_cell_32_679:
    vmulss xmm1, xmm5, DWORD PTR [r12+rax*4-8064]
__sbr_cell_32_679_end:
__sbr_cell_32_680:
    vmulss xmm2, xmm6, DWORD PTR [r12+rax*4-8256]
__sbr_cell_32_680_end:
__sbr_cell_32_681:
    vmulss xmm3, xmm7, DWORD PTR [r12+rax*4-8448]
__sbr_cell_32_681_end:
__sbr_cell_32_682:
    vaddss xmm1, xmm1, xmm2
__sbr_cell_32_682_end:
__sbr_cell_32_683:
    vaddss xmm1, xmm1, xmm3
__sbr_cell_32_683_end:
__sbr_cell_32_684:
    vmulss xmm2, xmm8, DWORD PTR [r12+rax*4-8640]
__sbr_cell_32_684_end:
sbr_hf_assemble.w1:
__sbr_cell_32_685:
    vaddss xmm1, xmm1, xmm2
__sbr_cell_32_685_end:
__sbr_cell_32_686:
    vmulss xmm2, xmm8, DWORD PTR [r12+rax*4-576]
__sbr_cell_32_686_end:
__sbr_cell_32_687:
    vaddss xmm0, xmm0, xmm2
__sbr_cell_32_687_end:
__sbr_cell_32_688:
    vmulss xmm2, xmm9, DWORD PTR [r12+rax*4-768]
__sbr_cell_32_688_end:
__sbr_cell_32_689:
    vmulss xmm3, xmm9, DWORD PTR [r12+rax*4-8832]
__sbr_cell_32_689_end:
__sbr_cell_32_690:
    vaddss xmm0, xmm0, xmm2
__sbr_cell_32_690_end:
__sbr_cell_32_691:
    vaddss xmm1, xmm1, xmm3
__sbr_cell_32_691_end:
__sbr_cell_32_692:
    vmovss DWORD PTR [rbp+rax*4-640], xmm1
__sbr_cell_32_692_end:
__sbr_cell_32_693:
    vmovss DWORD PTR [rbp+rax*4-448], xmm0
__sbr_cell_32_693_end:
__sbr_cell_32_694:
    inc rax
__sbr_cell_32_694_end:
__sbr_cell_32_695:
    cmp rcx, rax
__sbr_cell_32_695_end:
__sbr_cell_32_696:
    jne sbr_hf_assemble.Lb340
__sbr_cell_32_696_end:
sbr_hf_assemble.w2:
__sbr_cell_32_697:
    lea rdx, [rbp-640]
__sbr_cell_32_697_end:
__sbr_cell_32_698:
    lea r13, [rbp-448]
__sbr_cell_32_698_end:
__sbr_cell_32_699:
    jmp sbr_hf_assemble.Lb01d
__sbr_cell_32_699_end:
__sbr_cell_32_700:
    .nops 1
__sbr_cell_32_700_end:
sbr_hf_assemble.Lb400:
__sbr_cell_32_701:
    mov eax, DWORD PTR [r8+8]
__sbr_cell_32_701_end:
__sbr_cell_32_702:
    cmp rdi, rax
__sbr_cell_32_702_end:
__sbr_cell_32_703:
    jae sbr_hf_assemble.Lb820
__sbr_cell_32_703_end:
__sbr_cell_32_704:
    add r14, 192
__sbr_cell_32_704_end:
__sbr_cell_32_705:
    mov r10, rdi
__sbr_cell_32_705_end:
__sbr_cell_32_706:
    cmp rdi, 8
__sbr_cell_32_706_end:
__sbr_cell_32_707:
    jne sbr_hf_assemble.Laf40
__sbr_cell_32_707_end:
__sbr_cell_32_708:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_32_708_end:
sbr_hf_assemble.Lb426:
__sbr_cell_32_709:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_709_end:
__sbr_cell_32_710:
    shl eax, 7
__sbr_cell_32_710_end:
__sbr_cell_32_711:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_711_end:
__sbr_cell_32_712:
    movzx ecx, BYTE PTR [r8+88741]
__sbr_cell_32_712_end:
__sbr_cell_32_713:
    shl ecx, 7
__sbr_cell_32_713_end:
__sbr_cell_32_714:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_32_714_end:
__sbr_cell_32_715:
    lea rsi, [r8+69936]
__sbr_cell_32_715_end:
sbr_hf_assemble.y1:
__sbr_cell_32_716:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+160]
__sbr_cell_32_716_end:
__sbr_cell_32_717:
    vmovups YMMWORD PTR [rsi+rax*1+160], ymm0
__sbr_cell_32_717_end:
__sbr_cell_32_718:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+128]
__sbr_cell_32_718_end:
__sbr_cell_32_719:
    vmovups YMMWORD PTR [rsi+rax*1+128], ymm0
__sbr_cell_32_719_end:
__sbr_cell_32_720:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+0]
__sbr_cell_32_720_end:
__sbr_cell_32_721:
    vmovups ymm1, YMMWORD PTR [rsi+rcx*1+32]
__sbr_cell_32_721_end:
__sbr_cell_32_722:
    vmovups ymm2, YMMWORD PTR [rsi+rcx*1+64]
__sbr_cell_32_722_end:
__sbr_cell_32_723:
    vmovups ymm3, YMMWORD PTR [rsi+rcx*1+96]
__sbr_cell_32_723_end:
__sbr_cell_32_724:
    vmovups YMMWORD PTR [rsi+rax*1+96], ymm3
__sbr_cell_32_724_end:
__sbr_cell_32_725:
    vmovups YMMWORD PTR [rsi+rax*1+64], ymm2
__sbr_cell_32_725_end:
__sbr_cell_32_726:
    vmovups YMMWORD PTR [rsi+rax*1+32], ymm1
__sbr_cell_32_726_end:
__sbr_cell_32_727:
    vmovups YMMWORD PTR [rsi+rax*1+0], ymm0
__sbr_cell_32_727_end:
sbr_hf_assemble.y2:
__sbr_cell_32_728:
    lea rdi, [r8+78000]
__sbr_cell_32_728_end:
__sbr_cell_32_729:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+160]
__sbr_cell_32_729_end:
__sbr_cell_32_730:
    vmovups YMMWORD PTR [rdi+rax*1+160], ymm0
__sbr_cell_32_730_end:
__sbr_cell_32_731:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+128]
__sbr_cell_32_731_end:
__sbr_cell_32_732:
    vmovups YMMWORD PTR [rdi+rax*1+128], ymm0
__sbr_cell_32_732_end:
__sbr_cell_32_733:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+0]
__sbr_cell_32_733_end:
__sbr_cell_32_734:
    vmovups ymm1, YMMWORD PTR [rdi+rcx*1+32]
__sbr_cell_32_734_end:
__sbr_cell_32_735:
    vmovups ymm2, YMMWORD PTR [rdi+rcx*1+64]
__sbr_cell_32_735_end:
__sbr_cell_32_736:
    vmovups ymm3, YMMWORD PTR [rdi+rcx*1+96]
__sbr_cell_32_736_end:
__sbr_cell_32_737:
    vmovups YMMWORD PTR [rdi+rax*1+96], ymm3
__sbr_cell_32_737_end:
__sbr_cell_32_738:
    vmovups YMMWORD PTR [rdi+rax*1+64], ymm2
__sbr_cell_32_738_end:
__sbr_cell_32_739:
    vmovups YMMWORD PTR [rdi+rax*1+32], ymm1
__sbr_cell_32_739_end:
__sbr_cell_32_740:
    vmovups YMMWORD PTR [rdi+rax*1+0], ymm0
__sbr_cell_32_740_end:
sbr_hf_assemble.y3:
__sbr_cell_32_741:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+352]
__sbr_cell_32_741_end:
__sbr_cell_32_742:
    vmovups YMMWORD PTR [rsi+rax*1+352], ymm0
__sbr_cell_32_742_end:
__sbr_cell_32_743:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+320]
__sbr_cell_32_743_end:
__sbr_cell_32_744:
    vmovups YMMWORD PTR [rsi+rax*1+320], ymm0
__sbr_cell_32_744_end:
__sbr_cell_32_745:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+192]
__sbr_cell_32_745_end:
__sbr_cell_32_746:
    vmovups ymm1, YMMWORD PTR [rsi+rcx*1+224]
__sbr_cell_32_746_end:
__sbr_cell_32_747:
    vmovups ymm2, YMMWORD PTR [rsi+rcx*1+256]
__sbr_cell_32_747_end:
__sbr_cell_32_748:
    vmovups ymm3, YMMWORD PTR [rsi+rcx*1+288]
__sbr_cell_32_748_end:
__sbr_cell_32_749:
    vmovups YMMWORD PTR [rsi+rax*1+288], ymm3
__sbr_cell_32_749_end:
__sbr_cell_32_750:
    vmovups YMMWORD PTR [rsi+rax*1+256], ymm2
__sbr_cell_32_750_end:
__sbr_cell_32_751:
    vmovups YMMWORD PTR [rsi+rax*1+224], ymm1
__sbr_cell_32_751_end:
__sbr_cell_32_752:
    vmovups YMMWORD PTR [rsi+rax*1+192], ymm0
__sbr_cell_32_752_end:
sbr_hf_assemble.y4:
__sbr_cell_32_753:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_753_end:
__sbr_cell_32_754:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_754_end:
__sbr_cell_32_755:
    shl eax, 7
__sbr_cell_32_755_end:
__sbr_cell_32_756:
    movzx ecx, BYTE PTR [r8+88741]
__sbr_cell_32_756_end:
__sbr_cell_32_757:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_32_757_end:
__sbr_cell_32_758:
    shl ecx, 7
__sbr_cell_32_758_end:
sbr_hf_assemble.y5:
__sbr_cell_32_759:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+352]
__sbr_cell_32_759_end:
__sbr_cell_32_760:
    vmovups YMMWORD PTR [rdi+rax*1+352], ymm0
__sbr_cell_32_760_end:
__sbr_cell_32_761:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+320]
__sbr_cell_32_761_end:
__sbr_cell_32_762:
    vmovups YMMWORD PTR [rdi+rax*1+320], ymm0
__sbr_cell_32_762_end:
__sbr_cell_32_763:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+192]
__sbr_cell_32_763_end:
__sbr_cell_32_764:
    vmovups ymm1, YMMWORD PTR [rdi+rcx*1+224]
__sbr_cell_32_764_end:
__sbr_cell_32_765:
    vmovups ymm2, YMMWORD PTR [rdi+rcx*1+256]
__sbr_cell_32_765_end:
__sbr_cell_32_766:
    vmovups ymm3, YMMWORD PTR [rdi+rcx*1+288]
__sbr_cell_32_766_end:
__sbr_cell_32_767:
    vmovups YMMWORD PTR [rdi+rax*1+288], ymm3
__sbr_cell_32_767_end:
__sbr_cell_32_768:
    vmovups YMMWORD PTR [rdi+rax*1+256], ymm2
__sbr_cell_32_768_end:
__sbr_cell_32_769:
    vmovups YMMWORD PTR [rdi+rax*1+224], ymm1
__sbr_cell_32_769_end:
__sbr_cell_32_770:
    vmovups YMMWORD PTR [rdi+rax*1+192], ymm0
__sbr_cell_32_770_end:
sbr_hf_assemble.y6:
__sbr_cell_32_771:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_771_end:
__sbr_cell_32_772:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_772_end:
__sbr_cell_32_773:
    shl eax, 7
__sbr_cell_32_773_end:
__sbr_cell_32_774:
    movzx ecx, BYTE PTR [r8+88741]
__sbr_cell_32_774_end:
__sbr_cell_32_775:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_32_775_end:
__sbr_cell_32_776:
    shl ecx, 7
__sbr_cell_32_776_end:
sbr_hf_assemble.y7:
__sbr_cell_32_777:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+544]
__sbr_cell_32_777_end:
__sbr_cell_32_778:
    vmovups YMMWORD PTR [rsi+rax*1+544], ymm0
__sbr_cell_32_778_end:
__sbr_cell_32_779:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+512]
__sbr_cell_32_779_end:
__sbr_cell_32_780:
    vmovups YMMWORD PTR [rsi+rax*1+512], ymm0
__sbr_cell_32_780_end:
__sbr_cell_32_781:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+384]
__sbr_cell_32_781_end:
__sbr_cell_32_782:
    vmovups ymm1, YMMWORD PTR [rsi+rcx*1+416]
__sbr_cell_32_782_end:
__sbr_cell_32_783:
    vmovups ymm2, YMMWORD PTR [rsi+rcx*1+448]
__sbr_cell_32_783_end:
__sbr_cell_32_784:
    vmovups ymm3, YMMWORD PTR [rsi+rcx*1+480]
__sbr_cell_32_784_end:
__sbr_cell_32_785:
    vmovups YMMWORD PTR [rsi+rax*1+480], ymm3
__sbr_cell_32_785_end:
__sbr_cell_32_786:
    vmovups YMMWORD PTR [rsi+rax*1+448], ymm2
__sbr_cell_32_786_end:
__sbr_cell_32_787:
    vmovups YMMWORD PTR [rsi+rax*1+416], ymm1
__sbr_cell_32_787_end:
__sbr_cell_32_788:
    vmovups YMMWORD PTR [rsi+rax*1+384], ymm0
__sbr_cell_32_788_end:
sbr_hf_assemble.y8:
__sbr_cell_32_789:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_789_end:
__sbr_cell_32_790:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_790_end:
__sbr_cell_32_791:
    shl eax, 7
__sbr_cell_32_791_end:
__sbr_cell_32_792:
    movzx ecx, BYTE PTR [r8+88741]
__sbr_cell_32_792_end:
__sbr_cell_32_793:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_32_793_end:
__sbr_cell_32_794:
    shl ecx, 7
__sbr_cell_32_794_end:
sbr_hf_assemble.y9:
__sbr_cell_32_795:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+544]
__sbr_cell_32_795_end:
__sbr_cell_32_796:
    vmovups YMMWORD PTR [rdi+rax*1+544], ymm0
__sbr_cell_32_796_end:
__sbr_cell_32_797:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+512]
__sbr_cell_32_797_end:
__sbr_cell_32_798:
    vmovups YMMWORD PTR [rdi+rax*1+512], ymm0
__sbr_cell_32_798_end:
__sbr_cell_32_799:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+384]
__sbr_cell_32_799_end:
__sbr_cell_32_800:
    vmovups ymm1, YMMWORD PTR [rdi+rcx*1+416]
__sbr_cell_32_800_end:
__sbr_cell_32_801:
    vmovups ymm2, YMMWORD PTR [rdi+rcx*1+448]
__sbr_cell_32_801_end:
__sbr_cell_32_802:
    vmovups ymm3, YMMWORD PTR [rdi+rcx*1+480]
__sbr_cell_32_802_end:
__sbr_cell_32_803:
    vmovups YMMWORD PTR [rdi+rax*1+480], ymm3
__sbr_cell_32_803_end:
__sbr_cell_32_804:
    vmovups YMMWORD PTR [rdi+rax*1+448], ymm2
__sbr_cell_32_804_end:
__sbr_cell_32_805:
    vmovups YMMWORD PTR [rdi+rax*1+416], ymm1
__sbr_cell_32_805_end:
__sbr_cell_32_806:
    vmovups YMMWORD PTR [rdi+rax*1+384], ymm0
__sbr_cell_32_806_end:
sbr_hf_assemble.y10:
__sbr_cell_32_807:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_807_end:
__sbr_cell_32_808:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_808_end:
__sbr_cell_32_809:
    shl eax, 7
__sbr_cell_32_809_end:
__sbr_cell_32_810:
    movzx ecx, BYTE PTR [r8+88741]
__sbr_cell_32_810_end:
__sbr_cell_32_811:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_32_811_end:
__sbr_cell_32_812:
    shl ecx, 7
__sbr_cell_32_812_end:
sbr_hf_assemble.y11:
__sbr_cell_32_813:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+736]
__sbr_cell_32_813_end:
__sbr_cell_32_814:
    vmovups YMMWORD PTR [rsi+rax*1+736], ymm0
__sbr_cell_32_814_end:
__sbr_cell_32_815:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+704]
__sbr_cell_32_815_end:
__sbr_cell_32_816:
    vmovups YMMWORD PTR [rsi+rax*1+704], ymm0
__sbr_cell_32_816_end:
__sbr_cell_32_817:
    vmovups ymm0, YMMWORD PTR [rsi+rcx*1+576]
__sbr_cell_32_817_end:
__sbr_cell_32_818:
    vmovups ymm1, YMMWORD PTR [rsi+rcx*1+608]
__sbr_cell_32_818_end:
__sbr_cell_32_819:
    vmovups ymm2, YMMWORD PTR [rsi+rcx*1+640]
__sbr_cell_32_819_end:
__sbr_cell_32_820:
    vmovups ymm3, YMMWORD PTR [rsi+rcx*1+672]
__sbr_cell_32_820_end:
__sbr_cell_32_821:
    vmovups YMMWORD PTR [rsi+rax*1+672], ymm3
__sbr_cell_32_821_end:
__sbr_cell_32_822:
    vmovups YMMWORD PTR [rsi+rax*1+640], ymm2
__sbr_cell_32_822_end:
__sbr_cell_32_823:
    vmovups YMMWORD PTR [rsi+rax*1+608], ymm1
__sbr_cell_32_823_end:
__sbr_cell_32_824:
    vmovups YMMWORD PTR [rsi+rax*1+576], ymm0
__sbr_cell_32_824_end:
sbr_hf_assemble.y12:
__sbr_cell_32_825:
    movzx eax, BYTE PTR [r8+88732]
__sbr_cell_32_825_end:
__sbr_cell_32_826:
    lea rax, [rax+rax*2+0]
__sbr_cell_32_826_end:
__sbr_cell_32_827:
    shl eax, 7
__sbr_cell_32_827_end:
__sbr_cell_32_828:
    movzx ecx, BYTE PTR [r8+88741]
__sbr_cell_32_828_end:
__sbr_cell_32_829:
    lea rcx, [rcx+rcx*2+0]
__sbr_cell_32_829_end:
__sbr_cell_32_830:
    shl ecx, 7
__sbr_cell_32_830_end:
sbr_hf_assemble.y13:
__sbr_cell_32_831:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+736]
__sbr_cell_32_831_end:
__sbr_cell_32_832:
    vmovups YMMWORD PTR [rdi+rax*1+736], ymm0
__sbr_cell_32_832_end:
__sbr_cell_32_833:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+704]
__sbr_cell_32_833_end:
__sbr_cell_32_834:
    vmovups YMMWORD PTR [rdi+rax*1+704], ymm0
__sbr_cell_32_834_end:
__sbr_cell_32_835:
    vmovups ymm0, YMMWORD PTR [rdi+rcx*1+576]
__sbr_cell_32_835_end:
__sbr_cell_32_836:
    vmovups ymm1, YMMWORD PTR [rdi+rcx*1+608]
__sbr_cell_32_836_end:
__sbr_cell_32_837:
    vmovups ymm2, YMMWORD PTR [rdi+rcx*1+640]
__sbr_cell_32_837_end:
__sbr_cell_32_838:
    vmovups ymm3, YMMWORD PTR [rdi+rcx*1+672]
__sbr_cell_32_838_end:
__sbr_cell_32_839:
    vmovups YMMWORD PTR [rdi+rax*1+672], ymm3
__sbr_cell_32_839_end:
__sbr_cell_32_840:
    vmovups YMMWORD PTR [rdi+rax*1+640], ymm2
__sbr_cell_32_840_end:
__sbr_cell_32_841:
    vmovups YMMWORD PTR [rdi+rax*1+608], ymm1
__sbr_cell_32_841_end:
__sbr_cell_32_842:
    vmovups YMMWORD PTR [rdi+rax*1+576], ymm0
__sbr_cell_32_842_end:
sbr_hf_assemble.y14:
__sbr_cell_32_843:
    mov edx, DWORD PTR [r8+8]
__sbr_cell_32_843_end:
__sbr_cell_32_844:
    test edx, edx
__sbr_cell_32_844_end:
__sbr_cell_32_845:
    jne sbr_hf_assemble.La8f6
__sbr_cell_32_845_end:
sbr_hf_assemble.Lb820:
__sbr_cell_32_846:
    vmovq QWORD PTR [r8+88748], xmm4
__sbr_cell_32_846_end:
__sbr_cell_32_847:
    add rsp, 600
__sbr_cell_32_847_end:
__sbr_cell_32_848:
    pop rbx
__sbr_cell_32_848_end:
__sbr_cell_32_849:
    pop r12
__sbr_cell_32_849_end:
__sbr_cell_32_850:
    pop r13
__sbr_cell_32_850_end:
__sbr_cell_32_851:
    pop r14
__sbr_cell_32_851_end:
__sbr_cell_32_852:
    pop r15
__sbr_cell_32_852_end:
__sbr_cell_32_853:
    pop rbp
__sbr_cell_32_853_end:
__sbr_cell_32_854:
    vzeroupper
__sbr_cell_32_854_end:
sbr_hf_assemble.done:
__sbr_cell_32_855:
    ret
__sbr_cell_32_855_end:
sbr_hf_assemble.Lb83e:
__sbr_cell_32_856:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_32_856_end:
sbr_hf_assemble.Lb843:
__sbr_cell_32_857:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_32_857_end:
sbr_hf_assemble.Lb848:
__sbr_cell_32_858:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_32_858_end:
sbr_hf_assemble.Lb84d:
__sbr_cell_32_859:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_32_859_end:
.size sbr_hf_assemble, .-sbr_hf_assemble
.section .text.sbr_hf_inverse_filter,"ax",@progbits
.globl sbr_hf_inverse_filter
.type sbr_hf_inverse_filter,@function
sbr_hf_inverse_filter:
__sbr_cell_33_0:
    push rbp
__sbr_cell_33_0_end:
__sbr_cell_33_1:
    mov rbp, rsp
__sbr_cell_33_1_end:
__sbr_cell_33_2:
    push r15
__sbr_cell_33_2_end:
__sbr_cell_33_3:
    push r14
__sbr_cell_33_3_end:
__sbr_cell_33_4:
    push r13
__sbr_cell_33_4_end:
__sbr_cell_33_5:
    push r12
__sbr_cell_33_5_end:
__sbr_cell_33_6:
    push rbx
__sbr_cell_33_6_end:
__sbr_cell_33_7:
    sub rsp, 72
__sbr_cell_33_7_end:
__sbr_cell_33_8:
    mov QWORD PTR [rbp-56], rdi
__sbr_cell_33_8_end:
__sbr_cell_33_9:
    test r8d, r8d
__sbr_cell_33_9_end:
__sbr_cell_33_10:
    jle sbr_hf_inverse_filter.Lc0dd
__sbr_cell_33_10_end:
sbr_hf_inverse_filter.e1:
__sbr_cell_33_11:
    mov rbx, rcx
__sbr_cell_33_11_end:
__sbr_cell_33_12:
    mov r14, rdx
__sbr_cell_33_12_end:
__sbr_cell_33_13:
    mov r15, rsi
__sbr_cell_33_13_end:
__sbr_cell_33_14:
    mov eax, r8d
__sbr_cell_33_14_end:
__sbr_cell_33_15:
    shl rax, 3
__sbr_cell_33_15_end:
__sbr_cell_33_16:
    mov QWORD PTR [rbp-48], rax
__sbr_cell_33_16_end:
__sbr_cell_33_17:
    xor r12d, r12d
__sbr_cell_33_17_end:
__sbr_cell_33_18:
    xor r13d, r13d
__sbr_cell_33_18_end:
__sbr_cell_33_19:
    jmp sbr_hf_inverse_filter.Lbf6f
__sbr_cell_33_19_end:
__sbr_cell_33_20:
    .nops 1
__sbr_cell_33_20_end:
sbr_hf_inverse_filter.Lbf40:
__sbr_cell_33_21:
    mov DWORD PTR [rax+0], 0
__sbr_cell_33_21_end:
__sbr_cell_33_22:
    mov DWORD PTR [r14+r12*1+4], 0
__sbr_cell_33_22_end:
__sbr_cell_33_23:
    mov QWORD PTR [r15+r12*1+0], 0
__sbr_cell_33_23_end:
sbr_hf_inverse_filter.Lbf57:
__sbr_cell_33_24:
    inc r13
__sbr_cell_33_24_end:
__sbr_cell_33_25:
    add r12, 8
__sbr_cell_33_25_end:
__sbr_cell_33_26:
    add rbx, 320
__sbr_cell_33_26_end:
__sbr_cell_33_27:
    cmp QWORD PTR [rbp-48], r12
__sbr_cell_33_27_end:
__sbr_cell_33_28:
    je sbr_hf_inverse_filter.Lc0dd
__sbr_cell_33_28_end:
sbr_hf_inverse_filter.Lbf6f:
__sbr_cell_33_29:
    mov rdi, rbx
__sbr_cell_33_29_end:
__sbr_cell_33_30:
    lea rsi, [rbp-112]
__sbr_cell_33_30_end:
__sbr_cell_33_31:
    mov rax, QWORD PTR [rbp-56]
__sbr_cell_33_31_end:
__sbr_cell_33_32:
    call QWORD PTR [rax+56]
__sbr_cell_33_32_end:
sbr_hf_inverse_filter.c1:
__sbr_cell_33_33:
    vxorps xmm7, xmm7, xmm7
__sbr_cell_33_33_end:
__sbr_cell_33_34:
    vmovss xmm0, DWORD PTR [rbp-96]
__sbr_cell_33_34_end:
__sbr_cell_33_35:
    vmulss xmm3, xmm0, DWORD PTR [rbp-72]
__sbr_cell_33_35_end:
__sbr_cell_33_36:
    vmovsd xmm2, QWORD PTR [rbp-88]
__sbr_cell_33_36_end:
__sbr_cell_33_37:
    vshufps xmm1, xmm2, xmm2, 225
__sbr_cell_33_37_end:
__sbr_cell_33_38:
    vmulps xmm4, xmm2, xmm2
__sbr_cell_33_38_end:
__sbr_cell_33_39:
    vmovshdup xmm5, xmm4
__sbr_cell_33_39_end:
__sbr_cell_33_40:
    vaddss xmm4, xmm4, xmm5
__sbr_cell_33_40_end:
__sbr_cell_33_41:
    vdivss xmm4, xmm4, DWORD PTR [rip+LCPI19_0]
__sbr_cell_33_41_end:
__sbr_cell_33_42:
    vaddss xmm3, xmm3, xmm4
__sbr_cell_33_42_end:
__sbr_cell_33_43:
    vucomiss xmm3, xmm7
__sbr_cell_33_43_end:
__sbr_cell_33_44:
    jne sbr_hf_inverse_filter.Lbfb5
__sbr_cell_33_44_end:
__sbr_cell_33_45:
    jnp sbr_hf_inverse_filter.Lc000
__sbr_cell_33_45_end:
sbr_hf_inverse_filter.Lbfb5:
__sbr_cell_33_46:
    vbroadcastss xmm4, DWORD PTR [rbp-112]
__sbr_cell_33_46_end:
__sbr_cell_33_47:
    vmulps xmm4, xmm2, xmm4
__sbr_cell_33_47_end:
__sbr_cell_33_48:
    vbroadcastss xmm5, DWORD PTR [rbp-108]
__sbr_cell_33_48_end:
__sbr_cell_33_49:
    vmulps xmm5, xmm1, xmm5
__sbr_cell_33_49_end:
__sbr_cell_33_50:
    vaddsubps xmm4, xmm4, xmm5
__sbr_cell_33_50_end:
__sbr_cell_33_51:
    vmovsd xmm5, QWORD PTR [rbp-104]
__sbr_cell_33_51_end:
__sbr_cell_33_52:
    vmovsldup xmm6, xmm0
__sbr_cell_33_52_end:
__sbr_cell_33_53:
    vmulps xmm5, xmm6, xmm5
__sbr_cell_33_53_end:
__sbr_cell_33_54:
    vsubps xmm4, xmm4, xmm5
__sbr_cell_33_54_end:
__sbr_cell_33_55:
    vmovsldup xmm3, xmm3
__sbr_cell_33_55_end:
__sbr_cell_33_56:
    vdivps xmm4, xmm4, xmm3
__sbr_cell_33_56_end:
__sbr_cell_33_57:
    vmovss DWORD PTR [r14+r12*1+0], xmm4
__sbr_cell_33_57_end:
__sbr_cell_33_58:
    vmovaps xmm3, xmm4
__sbr_cell_33_58_end:
__sbr_cell_33_59:
    jmp sbr_hf_inverse_filter.Lc010
__sbr_cell_33_59_end:
__sbr_cell_33_60:
    .nops 1
__sbr_cell_33_60_end:
sbr_hf_inverse_filter.Lc000:
__sbr_cell_33_61:
    mov DWORD PTR [r14+r12*1+0], 0
__sbr_cell_33_61_end:
__sbr_cell_33_62:
    vxorps xmm3, xmm3, xmm3
__sbr_cell_33_62_end:
__sbr_cell_33_63:
    vxorps xmm4, xmm4, xmm4
__sbr_cell_33_63_end:
sbr_hf_inverse_filter.Lc010:
__sbr_cell_33_64:
    vmovshdup xmm5, xmm3
__sbr_cell_33_64_end:
__sbr_cell_33_65:
    vmovss DWORD PTR [r14+r12*1+4], xmm5
__sbr_cell_33_65_end:
__sbr_cell_33_66:
    vucomiss xmm0, xmm7
__sbr_cell_33_66_end:
__sbr_cell_33_67:
    vmovss xmm6, DWORD PTR [rip+LCPI19_1]
__sbr_cell_33_67_end:
__sbr_cell_33_68:
    jne sbr_hf_inverse_filter.Lc02f
__sbr_cell_33_68_end:
__sbr_cell_33_69:
    jnp sbr_hf_inverse_filter.Lc0b0
__sbr_cell_33_69_end:
sbr_hf_inverse_filter.Lc02f:
__sbr_cell_33_70:
    vmulss xmm4, xmm2, xmm4
__sbr_cell_33_70_end:
__sbr_cell_33_71:
    vaddss xmm4, xmm4, DWORD PTR [rbp-112]
__sbr_cell_33_71_end:
__sbr_cell_33_72:
    vmovshdup xmm2, xmm2
__sbr_cell_33_72_end:
__sbr_cell_33_73:
    vmulss xmm2, xmm2, xmm5
__sbr_cell_33_73_end:
__sbr_cell_33_74:
    vaddss xmm2, xmm4, xmm2
__sbr_cell_33_74_end:
__sbr_cell_33_75:
    vxorps xmm2, xmm2, XMMWORD PTR [rip+LCPI19_2]
__sbr_cell_33_75_end:
__sbr_cell_33_76:
    vmulps xmm1, xmm1, xmm3
__sbr_cell_33_76_end:
__sbr_cell_33_77:
    vmovshdup xmm3, xmm1
__sbr_cell_33_77_end:
__sbr_cell_33_78:
    vaddss xmm3, xmm3, DWORD PTR [rbp-108]
__sbr_cell_33_78_end:
__sbr_cell_33_79:
    vsubss xmm1, xmm1, xmm3
__sbr_cell_33_79_end:
__sbr_cell_33_80:
    vinsertps xmm1, xmm2, xmm1, 28
__sbr_cell_33_80_end:
__sbr_cell_33_81:
    vmovsldup xmm0, xmm0
__sbr_cell_33_81_end:
__sbr_cell_33_82:
    vdivps xmm0, xmm1, xmm0
__sbr_cell_33_82_end:
__sbr_cell_33_83:
    vmovlps QWORD PTR [r15+r12*1+0], xmm0
__sbr_cell_33_83_end:
sbr_hf_inverse_filter.c2:
__sbr_cell_33_84:
    lea rax, [r14+r13*8+0]
__sbr_cell_33_84_end:
__sbr_cell_33_85:
    vmovsd xmm1, QWORD PTR [r14+r12*1+0]
__sbr_cell_33_85_end:
__sbr_cell_33_86:
    vmulps xmm1, xmm1, xmm1
__sbr_cell_33_86_end:
__sbr_cell_33_87:
    vmovshdup xmm2, xmm1
__sbr_cell_33_87_end:
__sbr_cell_33_88:
    vaddss xmm1, xmm1, xmm2
__sbr_cell_33_88_end:
__sbr_cell_33_89:
    vucomiss xmm1, xmm6
__sbr_cell_33_89_end:
__sbr_cell_33_90:
    jae sbr_hf_inverse_filter.Lbf40
__sbr_cell_33_90_end:
__sbr_cell_33_91:
    vmulps xmm0, xmm0, xmm0
__sbr_cell_33_91_end:
__sbr_cell_33_92:
    vmovshdup xmm1, xmm0
__sbr_cell_33_92_end:
__sbr_cell_33_93:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_33_93_end:
__sbr_cell_33_94:
    vucomiss xmm0, xmm6
__sbr_cell_33_94_end:
__sbr_cell_33_95:
    jb sbr_hf_inverse_filter.Lbf57
__sbr_cell_33_95_end:
__sbr_cell_33_96:
    jmp sbr_hf_inverse_filter.Lbf40
__sbr_cell_33_96_end:
__sbr_cell_33_97:
    .nops 1
__sbr_cell_33_97_end:
sbr_hf_inverse_filter.Lc0b0:
__sbr_cell_33_98:
    mov QWORD PTR [r15+r12*1+0], 0
__sbr_cell_33_98_end:
__sbr_cell_33_99:
    vmovsd xmm0, QWORD PTR [r14+r12*1+0]
__sbr_cell_33_99_end:
__sbr_cell_33_100:
    vmulps xmm0, xmm0, xmm0
__sbr_cell_33_100_end:
__sbr_cell_33_101:
    vmovshdup xmm1, xmm0
__sbr_cell_33_101_end:
__sbr_cell_33_102:
    vaddss xmm0, xmm0, xmm1
__sbr_cell_33_102_end:
__sbr_cell_33_103:
    vucomiss xmm0, xmm6
__sbr_cell_33_103_end:
__sbr_cell_33_104:
    jb sbr_hf_inverse_filter.Lbf57
__sbr_cell_33_104_end:
__sbr_cell_33_105:
    lea rax, [r14+r12*1+0]
__sbr_cell_33_105_end:
__sbr_cell_33_106:
    jmp sbr_hf_inverse_filter.Lbf40
__sbr_cell_33_106_end:
sbr_hf_inverse_filter.Lc0dd:
__sbr_cell_33_107:
    add rsp, 72
__sbr_cell_33_107_end:
__sbr_cell_33_108:
    pop rbx
__sbr_cell_33_108_end:
__sbr_cell_33_109:
    pop r12
__sbr_cell_33_109_end:
__sbr_cell_33_110:
    pop r13
__sbr_cell_33_110_end:
__sbr_cell_33_111:
    pop r14
__sbr_cell_33_111_end:
__sbr_cell_33_112:
    pop r15
__sbr_cell_33_112_end:
__sbr_cell_33_113:
    pop rbp
__sbr_cell_33_113_end:
sbr_hf_inverse_filter.done:
__sbr_cell_33_114:
    ret
__sbr_cell_33_114_end:
.size sbr_hf_inverse_filter, .-sbr_hf_inverse_filter
.section .text.sbr_lf_gen,"ax",@progbits
.globl sbr_lf_gen
.type sbr_lf_gen,@function
sbr_lf_gen:
__sbr_cell_34_0:
    push rbp
__sbr_cell_34_0_end:
__sbr_cell_34_1:
    mov rbp, rsp
__sbr_cell_34_1_end:
__sbr_cell_34_2:
    push r15
__sbr_cell_34_2_end:
__sbr_cell_34_3:
    push r14
__sbr_cell_34_3_end:
__sbr_cell_34_4:
    push r12
__sbr_cell_34_4_end:
__sbr_cell_34_5:
    push rbx
__sbr_cell_34_5_end:
__sbr_cell_34_6:
    mov r12d, ecx
__sbr_cell_34_6_end:
__sbr_cell_34_7:
    mov rbx, rdx
__sbr_cell_34_7_end:
__sbr_cell_34_8:
    mov r14, rsi
__sbr_cell_34_8_end:
__sbr_cell_34_9:
    mov r15, rdi
__sbr_cell_34_9_end:
sbr_lf_gen.c:
__sbr_cell_34_10:
    mov edx, 10240
__sbr_cell_34_10_end:
__sbr_cell_34_11:
    mov rdi, rsi
__sbr_cell_34_11_end:
__sbr_cell_34_12:
    xor esi, esi
__sbr_cell_34_12_end:
__sbr_cell_34_13:
    call memset
__sbr_cell_34_13_end:
sbr_lf_gen.m1:
__sbr_cell_34_14:
    cmp DWORD PTR [r15+88], 0
__sbr_cell_34_14_end:
__sbr_cell_34_15:
    movsxd rax, r12d
__sbr_cell_34_15_end:
__sbr_cell_34_16:
    je sbr_lf_gen.La588
__sbr_cell_34_16_end:
__sbr_cell_34_17:
    mov rcx, rax
__sbr_cell_34_17_end:
__sbr_cell_34_18:
    shl rcx, 13
__sbr_cell_34_18_end:
__sbr_cell_34_19:
    add rcx, rbx
__sbr_cell_34_19_end:
__sbr_cell_34_20:
    lea rdx, [r14+316]
__sbr_cell_34_20_end:
__sbr_cell_34_21:
    mov esi, 1
__sbr_cell_34_21_end:
__sbr_cell_34_22:
    .nops 1
__sbr_cell_34_22_end:
sbr_lf_gen.La190:
__sbr_cell_34_23:
    vmovss xmm0, DWORD PTR [rcx+rsi*8-8]
__sbr_cell_34_23_end:
__sbr_cell_34_24:
    vmovss DWORD PTR [rdx-252], xmm0
__sbr_cell_34_24_end:
__sbr_cell_34_25:
    vmovss xmm0, DWORD PTR [rcx+rsi*8-4]
__sbr_cell_34_25_end:
__sbr_cell_34_26:
    vmovss DWORD PTR [rdx-248], xmm0
__sbr_cell_34_26_end:
__sbr_cell_34_27:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+248]
__sbr_cell_34_27_end:
__sbr_cell_34_28:
    vmovss DWORD PTR [rdx-244], xmm0
__sbr_cell_34_28_end:
__sbr_cell_34_29:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+252]
__sbr_cell_34_29_end:
__sbr_cell_34_30:
    vmovss DWORD PTR [rdx-240], xmm0
__sbr_cell_34_30_end:
__sbr_cell_34_31:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+504]
__sbr_cell_34_31_end:
__sbr_cell_34_32:
    vmovss DWORD PTR [rdx-236], xmm0
__sbr_cell_34_32_end:
__sbr_cell_34_33:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+508]
__sbr_cell_34_33_end:
__sbr_cell_34_34:
    vmovss DWORD PTR [rdx-232], xmm0
__sbr_cell_34_34_end:
__sbr_cell_34_35:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+760]
__sbr_cell_34_35_end:
__sbr_cell_34_36:
    vmovss DWORD PTR [rdx-228], xmm0
__sbr_cell_34_36_end:
__sbr_cell_34_37:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+764]
__sbr_cell_34_37_end:
__sbr_cell_34_38:
    vmovss DWORD PTR [rdx-224], xmm0
__sbr_cell_34_38_end:
sbr_lf_gen.a1:
__sbr_cell_34_39:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1016]
__sbr_cell_34_39_end:
__sbr_cell_34_40:
    vmovss DWORD PTR [rdx-220], xmm0
__sbr_cell_34_40_end:
__sbr_cell_34_41:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1020]
__sbr_cell_34_41_end:
__sbr_cell_34_42:
    vmovss DWORD PTR [rdx-216], xmm0
__sbr_cell_34_42_end:
__sbr_cell_34_43:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1272]
__sbr_cell_34_43_end:
__sbr_cell_34_44:
    vmovss DWORD PTR [rdx-212], xmm0
__sbr_cell_34_44_end:
__sbr_cell_34_45:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1276]
__sbr_cell_34_45_end:
__sbr_cell_34_46:
    vmovss DWORD PTR [rdx-208], xmm0
__sbr_cell_34_46_end:
__sbr_cell_34_47:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1528]
__sbr_cell_34_47_end:
__sbr_cell_34_48:
    vmovss DWORD PTR [rdx-204], xmm0
__sbr_cell_34_48_end:
__sbr_cell_34_49:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1532]
__sbr_cell_34_49_end:
__sbr_cell_34_50:
    vmovss DWORD PTR [rdx-200], xmm0
__sbr_cell_34_50_end:
__sbr_cell_34_51:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1784]
__sbr_cell_34_51_end:
__sbr_cell_34_52:
    vmovss DWORD PTR [rdx-196], xmm0
__sbr_cell_34_52_end:
__sbr_cell_34_53:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+1788]
__sbr_cell_34_53_end:
__sbr_cell_34_54:
    vmovss DWORD PTR [rdx-192], xmm0
__sbr_cell_34_54_end:
sbr_lf_gen.a2:
__sbr_cell_34_55:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2040]
__sbr_cell_34_55_end:
__sbr_cell_34_56:
    vmovss DWORD PTR [rdx-188], xmm0
__sbr_cell_34_56_end:
__sbr_cell_34_57:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2044]
__sbr_cell_34_57_end:
__sbr_cell_34_58:
    vmovss DWORD PTR [rdx-184], xmm0
__sbr_cell_34_58_end:
__sbr_cell_34_59:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2296]
__sbr_cell_34_59_end:
__sbr_cell_34_60:
    vmovss DWORD PTR [rdx-180], xmm0
__sbr_cell_34_60_end:
__sbr_cell_34_61:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2300]
__sbr_cell_34_61_end:
__sbr_cell_34_62:
    vmovss DWORD PTR [rdx-176], xmm0
__sbr_cell_34_62_end:
__sbr_cell_34_63:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2552]
__sbr_cell_34_63_end:
__sbr_cell_34_64:
    vmovss DWORD PTR [rdx-172], xmm0
__sbr_cell_34_64_end:
__sbr_cell_34_65:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2556]
__sbr_cell_34_65_end:
__sbr_cell_34_66:
    vmovss DWORD PTR [rdx-168], xmm0
__sbr_cell_34_66_end:
__sbr_cell_34_67:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2808]
__sbr_cell_34_67_end:
__sbr_cell_34_68:
    vmovss DWORD PTR [rdx-164], xmm0
__sbr_cell_34_68_end:
__sbr_cell_34_69:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+2812]
__sbr_cell_34_69_end:
__sbr_cell_34_70:
    vmovss DWORD PTR [rdx-160], xmm0
__sbr_cell_34_70_end:
sbr_lf_gen.a3:
__sbr_cell_34_71:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3064]
__sbr_cell_34_71_end:
__sbr_cell_34_72:
    vmovss DWORD PTR [rdx-156], xmm0
__sbr_cell_34_72_end:
__sbr_cell_34_73:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3068]
__sbr_cell_34_73_end:
__sbr_cell_34_74:
    vmovss DWORD PTR [rdx-152], xmm0
__sbr_cell_34_74_end:
__sbr_cell_34_75:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3320]
__sbr_cell_34_75_end:
__sbr_cell_34_76:
    vmovss DWORD PTR [rdx-148], xmm0
__sbr_cell_34_76_end:
__sbr_cell_34_77:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3324]
__sbr_cell_34_77_end:
__sbr_cell_34_78:
    vmovss DWORD PTR [rdx-144], xmm0
__sbr_cell_34_78_end:
__sbr_cell_34_79:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3576]
__sbr_cell_34_79_end:
__sbr_cell_34_80:
    vmovss DWORD PTR [rdx-140], xmm0
__sbr_cell_34_80_end:
__sbr_cell_34_81:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3580]
__sbr_cell_34_81_end:
__sbr_cell_34_82:
    vmovss DWORD PTR [rdx-136], xmm0
__sbr_cell_34_82_end:
__sbr_cell_34_83:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3832]
__sbr_cell_34_83_end:
__sbr_cell_34_84:
    vmovss DWORD PTR [rdx-132], xmm0
__sbr_cell_34_84_end:
__sbr_cell_34_85:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+3836]
__sbr_cell_34_85_end:
__sbr_cell_34_86:
    vmovss DWORD PTR [rdx-128], xmm0
__sbr_cell_34_86_end:
sbr_lf_gen.a4:
__sbr_cell_34_87:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4088]
__sbr_cell_34_87_end:
__sbr_cell_34_88:
    vmovss DWORD PTR [rdx-124], xmm0
__sbr_cell_34_88_end:
__sbr_cell_34_89:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4092]
__sbr_cell_34_89_end:
__sbr_cell_34_90:
    vmovss DWORD PTR [rdx-120], xmm0
__sbr_cell_34_90_end:
__sbr_cell_34_91:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4344]
__sbr_cell_34_91_end:
__sbr_cell_34_92:
    vmovss DWORD PTR [rdx-116], xmm0
__sbr_cell_34_92_end:
__sbr_cell_34_93:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4348]
__sbr_cell_34_93_end:
__sbr_cell_34_94:
    vmovss DWORD PTR [rdx-112], xmm0
__sbr_cell_34_94_end:
__sbr_cell_34_95:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4600]
__sbr_cell_34_95_end:
__sbr_cell_34_96:
    vmovss DWORD PTR [rdx-108], xmm0
__sbr_cell_34_96_end:
__sbr_cell_34_97:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4604]
__sbr_cell_34_97_end:
__sbr_cell_34_98:
    vmovss DWORD PTR [rdx-104], xmm0
__sbr_cell_34_98_end:
__sbr_cell_34_99:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4856]
__sbr_cell_34_99_end:
__sbr_cell_34_100:
    vmovss DWORD PTR [rdx-100], xmm0
__sbr_cell_34_100_end:
__sbr_cell_34_101:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+4860]
__sbr_cell_34_101_end:
__sbr_cell_34_102:
    vmovss DWORD PTR [rdx-96], xmm0
__sbr_cell_34_102_end:
sbr_lf_gen.a5:
__sbr_cell_34_103:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5112]
__sbr_cell_34_103_end:
__sbr_cell_34_104:
    vmovss DWORD PTR [rdx-92], xmm0
__sbr_cell_34_104_end:
__sbr_cell_34_105:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5116]
__sbr_cell_34_105_end:
__sbr_cell_34_106:
    vmovss DWORD PTR [rdx-88], xmm0
__sbr_cell_34_106_end:
__sbr_cell_34_107:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5368]
__sbr_cell_34_107_end:
__sbr_cell_34_108:
    vmovss DWORD PTR [rdx-84], xmm0
__sbr_cell_34_108_end:
__sbr_cell_34_109:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5372]
__sbr_cell_34_109_end:
__sbr_cell_34_110:
    vmovss DWORD PTR [rdx-80], xmm0
__sbr_cell_34_110_end:
__sbr_cell_34_111:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5624]
__sbr_cell_34_111_end:
__sbr_cell_34_112:
    vmovss DWORD PTR [rdx-76], xmm0
__sbr_cell_34_112_end:
__sbr_cell_34_113:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5628]
__sbr_cell_34_113_end:
__sbr_cell_34_114:
    vmovss DWORD PTR [rdx-72], xmm0
__sbr_cell_34_114_end:
__sbr_cell_34_115:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5880]
__sbr_cell_34_115_end:
__sbr_cell_34_116:
    vmovss DWORD PTR [rdx-68], xmm0
__sbr_cell_34_116_end:
__sbr_cell_34_117:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+5884]
__sbr_cell_34_117_end:
__sbr_cell_34_118:
    vmovss DWORD PTR [rdx-64], xmm0
__sbr_cell_34_118_end:
sbr_lf_gen.a6:
__sbr_cell_34_119:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6136]
__sbr_cell_34_119_end:
__sbr_cell_34_120:
    vmovss DWORD PTR [rdx-60], xmm0
__sbr_cell_34_120_end:
__sbr_cell_34_121:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6140]
__sbr_cell_34_121_end:
__sbr_cell_34_122:
    vmovss DWORD PTR [rdx-56], xmm0
__sbr_cell_34_122_end:
__sbr_cell_34_123:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6392]
__sbr_cell_34_123_end:
__sbr_cell_34_124:
    vmovss DWORD PTR [rdx-52], xmm0
__sbr_cell_34_124_end:
__sbr_cell_34_125:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6396]
__sbr_cell_34_125_end:
__sbr_cell_34_126:
    vmovss DWORD PTR [rdx-48], xmm0
__sbr_cell_34_126_end:
__sbr_cell_34_127:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6648]
__sbr_cell_34_127_end:
__sbr_cell_34_128:
    vmovss DWORD PTR [rdx-44], xmm0
__sbr_cell_34_128_end:
__sbr_cell_34_129:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6652]
__sbr_cell_34_129_end:
__sbr_cell_34_130:
    vmovss DWORD PTR [rdx-40], xmm0
__sbr_cell_34_130_end:
__sbr_cell_34_131:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6904]
__sbr_cell_34_131_end:
__sbr_cell_34_132:
    vmovss DWORD PTR [rdx-36], xmm0
__sbr_cell_34_132_end:
__sbr_cell_34_133:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+6908]
__sbr_cell_34_133_end:
__sbr_cell_34_134:
    vmovss DWORD PTR [rdx-32], xmm0
__sbr_cell_34_134_end:
sbr_lf_gen.a7:
__sbr_cell_34_135:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7160]
__sbr_cell_34_135_end:
__sbr_cell_34_136:
    vmovss DWORD PTR [rdx-28], xmm0
__sbr_cell_34_136_end:
__sbr_cell_34_137:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7164]
__sbr_cell_34_137_end:
__sbr_cell_34_138:
    vmovss DWORD PTR [rdx-24], xmm0
__sbr_cell_34_138_end:
__sbr_cell_34_139:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7416]
__sbr_cell_34_139_end:
__sbr_cell_34_140:
    vmovss DWORD PTR [rdx-20], xmm0
__sbr_cell_34_140_end:
__sbr_cell_34_141:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7420]
__sbr_cell_34_141_end:
__sbr_cell_34_142:
    vmovss DWORD PTR [rdx-16], xmm0
__sbr_cell_34_142_end:
__sbr_cell_34_143:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7672]
__sbr_cell_34_143_end:
__sbr_cell_34_144:
    vmovss DWORD PTR [rdx-12], xmm0
__sbr_cell_34_144_end:
__sbr_cell_34_145:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7676]
__sbr_cell_34_145_end:
__sbr_cell_34_146:
    vmovss DWORD PTR [rdx-8], xmm0
__sbr_cell_34_146_end:
__sbr_cell_34_147:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7928]
__sbr_cell_34_147_end:
__sbr_cell_34_148:
    vmovss DWORD PTR [rdx-4], xmm0
__sbr_cell_34_148_end:
__sbr_cell_34_149:
    vmovss xmm0, DWORD PTR [rcx+rsi*8+7932]
__sbr_cell_34_149_end:
__sbr_cell_34_150:
    vmovss DWORD PTR [rdx+0], xmm0
__sbr_cell_34_150_end:
sbr_lf_gen.a8:
__sbr_cell_34_151:
    mov edi, DWORD PTR [r15+88]
__sbr_cell_34_151_end:
__sbr_cell_34_152:
    cmp rsi, rdi
__sbr_cell_34_152_end:
__sbr_cell_34_153:
    jae sbr_lf_gen.La588
__sbr_cell_34_153_end:
__sbr_cell_34_154:
    inc rsi
__sbr_cell_34_154_end:
__sbr_cell_34_155:
    add rdx, 320
__sbr_cell_34_155_end:
__sbr_cell_34_156:
    cmp rsi, 33
__sbr_cell_34_156_end:
__sbr_cell_34_157:
    jne sbr_lf_gen.La190
__sbr_cell_34_157_end:
sbr_lf_gen.t1:
__sbr_cell_34_158:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_34_158_end:
sbr_lf_gen.La588:
__sbr_cell_34_159:
    cmp DWORD PTR [r15+84], 0
__sbr_cell_34_159_end:
__sbr_cell_34_160:
    je sbr_lf_gen.La6ba
__sbr_cell_34_160_end:
__sbr_cell_34_161:
    add r14, 60
__sbr_cell_34_161_end:
__sbr_cell_34_162:
    shl rax, 13
__sbr_cell_34_162_end:
__sbr_cell_34_163:
    sub rbx, rax
__sbr_cell_34_163_end:
__sbr_cell_34_164:
    add rbx, 16132
__sbr_cell_34_164_end:
__sbr_cell_34_165:
    mov rax, -32
__sbr_cell_34_165_end:
__sbr_cell_34_166:
    .nops 1
__sbr_cell_34_166_end:
sbr_lf_gen.La5b0:
__sbr_cell_34_167:
    vmovss xmm0, DWORD PTR [rbx+rax*8-1540]
__sbr_cell_34_167_end:
__sbr_cell_34_168:
    vmovss DWORD PTR [r14-60], xmm0
__sbr_cell_34_168_end:
__sbr_cell_34_169:
    vmovss xmm0, DWORD PTR [rbx+rax*8-1536]
__sbr_cell_34_169_end:
__sbr_cell_34_170:
    vmovss DWORD PTR [r14-56], xmm0
__sbr_cell_34_170_end:
__sbr_cell_34_171:
    vmovss xmm0, DWORD PTR [rbx+rax*8-1284]
__sbr_cell_34_171_end:
__sbr_cell_34_172:
    vmovss DWORD PTR [r14-52], xmm0
__sbr_cell_34_172_end:
__sbr_cell_34_173:
    vmovss xmm0, DWORD PTR [rbx+rax*8-1280]
__sbr_cell_34_173_end:
__sbr_cell_34_174:
    vmovss DWORD PTR [r14-48], xmm0
__sbr_cell_34_174_end:
__sbr_cell_34_175:
    vmovss xmm0, DWORD PTR [rbx+rax*8-1028]
__sbr_cell_34_175_end:
__sbr_cell_34_176:
    vmovss DWORD PTR [r14-44], xmm0
__sbr_cell_34_176_end:
__sbr_cell_34_177:
    vmovss xmm0, DWORD PTR [rbx+rax*8-1024]
__sbr_cell_34_177_end:
__sbr_cell_34_178:
    vmovss DWORD PTR [r14-40], xmm0
__sbr_cell_34_178_end:
__sbr_cell_34_179:
    vmovss xmm0, DWORD PTR [rbx+rax*8-772]
__sbr_cell_34_179_end:
__sbr_cell_34_180:
    vmovss DWORD PTR [r14-36], xmm0
__sbr_cell_34_180_end:
__sbr_cell_34_181:
    vmovss xmm0, DWORD PTR [rbx+rax*8-768]
__sbr_cell_34_181_end:
__sbr_cell_34_182:
    vmovss DWORD PTR [r14-32], xmm0
__sbr_cell_34_182_end:
sbr_lf_gen.b1:
__sbr_cell_34_183:
    vmovss xmm0, DWORD PTR [rbx+rax*8-516]
__sbr_cell_34_183_end:
__sbr_cell_34_184:
    vmovss DWORD PTR [r14-28], xmm0
__sbr_cell_34_184_end:
__sbr_cell_34_185:
    vmovss xmm0, DWORD PTR [rbx+rax*8-512]
__sbr_cell_34_185_end:
__sbr_cell_34_186:
    vmovss DWORD PTR [r14-24], xmm0
__sbr_cell_34_186_end:
__sbr_cell_34_187:
    vmovss xmm0, DWORD PTR [rbx+rax*8-260]
__sbr_cell_34_187_end:
__sbr_cell_34_188:
    vmovss DWORD PTR [r14-20], xmm0
__sbr_cell_34_188_end:
__sbr_cell_34_189:
    vmovss xmm0, DWORD PTR [rbx+rax*8-256]
__sbr_cell_34_189_end:
__sbr_cell_34_190:
    vmovss DWORD PTR [r14-16], xmm0
__sbr_cell_34_190_end:
__sbr_cell_34_191:
    vmovss xmm0, DWORD PTR [rbx+rax*8-4]
__sbr_cell_34_191_end:
__sbr_cell_34_192:
    vmovss DWORD PTR [r14-12], xmm0
__sbr_cell_34_192_end:
__sbr_cell_34_193:
    vmovss xmm0, DWORD PTR [rbx+rax*8+0]
__sbr_cell_34_193_end:
__sbr_cell_34_194:
    vmovss DWORD PTR [r14-8], xmm0
__sbr_cell_34_194_end:
__sbr_cell_34_195:
    vmovss xmm0, DWORD PTR [rbx+rax*8+252]
__sbr_cell_34_195_end:
__sbr_cell_34_196:
    vmovss DWORD PTR [r14-4], xmm0
__sbr_cell_34_196_end:
__sbr_cell_34_197:
    vmovss xmm0, DWORD PTR [rbx+rax*8+256]
__sbr_cell_34_197_end:
__sbr_cell_34_198:
    vmovss DWORD PTR [r14+0], xmm0
__sbr_cell_34_198_end:
sbr_lf_gen.b2:
__sbr_cell_34_199:
    lea rcx, [rax+33]
__sbr_cell_34_199_end:
__sbr_cell_34_200:
    mov edx, DWORD PTR [r15+84]
__sbr_cell_34_200_end:
__sbr_cell_34_201:
    cmp rcx, rdx
__sbr_cell_34_201_end:
__sbr_cell_34_202:
    jae sbr_lf_gen.La6ba
__sbr_cell_34_202_end:
__sbr_cell_34_203:
    add r14, 320
__sbr_cell_34_203_end:
__sbr_cell_34_204:
    inc rax
__sbr_cell_34_204_end:
__sbr_cell_34_205:
    jne sbr_lf_gen.La5b0
__sbr_cell_34_205_end:
sbr_lf_gen.t2:
__sbr_cell_34_206:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_34_206_end:
sbr_lf_gen.La6ba:
__sbr_cell_34_207:
    xor eax, eax
__sbr_cell_34_207_end:
__sbr_cell_34_208:
    pop rbx
__sbr_cell_34_208_end:
__sbr_cell_34_209:
    pop r12
__sbr_cell_34_209_end:
__sbr_cell_34_210:
    pop r14
__sbr_cell_34_210_end:
__sbr_cell_34_211:
    pop r15
__sbr_cell_34_211_end:
__sbr_cell_34_212:
    pop rbp
__sbr_cell_34_212_end:
sbr_lf_gen.done:
__sbr_cell_34_213:
    ret
__sbr_cell_34_213_end:
__sbr_cell_34_214:
    int3
__sbr_cell_34_214_end:
__sbr_cell_34_215:
    int3
__sbr_cell_34_215_end:
__sbr_cell_34_216:
    int3
__sbr_cell_34_216_end:
__sbr_cell_34_217:
    int3
__sbr_cell_34_217_end:
__sbr_cell_34_218:
    int3
__sbr_cell_34_218_end:
__sbr_cell_34_219:
    int3
__sbr_cell_34_219_end:
__sbr_cell_34_220:
    int3
__sbr_cell_34_220_end:
__sbr_cell_34_221:
    int3
__sbr_cell_34_221_end:
__sbr_cell_34_222:
    int3
__sbr_cell_34_222_end:
__sbr_cell_34_223:
    int3
__sbr_cell_34_223_end:
__sbr_cell_34_224:
    int3
__sbr_cell_34_224_end:
.size sbr_lf_gen, .-sbr_lf_gen
.section .text.sbr_make_f_tablelim,"ax",@progbits
.globl sbr_make_f_tablelim
.type sbr_make_f_tablelim,@function
sbr_make_f_tablelim:
__sbr_cell_35_0:
    push rbp
__sbr_cell_35_0_end:
__sbr_cell_35_1:
    mov rbp, rsp
__sbr_cell_35_1_end:
__sbr_cell_35_2:
    push r15
__sbr_cell_35_2_end:
__sbr_cell_35_3:
    push r14
__sbr_cell_35_3_end:
__sbr_cell_35_4:
    push r12
__sbr_cell_35_4_end:
__sbr_cell_35_5:
    push rbx
__sbr_cell_35_5_end:
__sbr_cell_35_6:
    sub rsp, 1056
__sbr_cell_35_6_end:
sbr_make_f_tablelim.L3f22:
__sbr_cell_35_7:
    mov rbx, rdi
__sbr_cell_35_7_end:
__sbr_cell_35_8:
    mov eax, DWORD PTR [rdi+44]
__sbr_cell_35_8_end:
__sbr_cell_35_9:
    test rax, rax
__sbr_cell_35_9_end:
__sbr_cell_35_10:
    je sbr_make_f_tablelim.L438a
__sbr_cell_35_10_end:
sbr_make_f_tablelim.L3f31:
__sbr_cell_35_11:
    cmp eax, 4
__sbr_cell_35_11_end:
__sbr_cell_35_12:
    jae sbr_make_f_tablelim.L43dc
__sbr_cell_35_12_end:
sbr_make_f_tablelim.L3f3a:
__sbr_cell_35_13:
    lea rcx, [rip+sbr_make_f_tablelim_bw]
__sbr_cell_35_13_end:
__sbr_cell_35_14:
    vmovss xmm0, DWORD PTR [rcx+rax*4-4]
__sbr_cell_35_14_end:
__sbr_cell_35_15:
    movzx eax, WORD PTR [rbx+88]
__sbr_cell_35_15_end:
__sbr_cell_35_16:
    mov WORD PTR [rbp-46], ax
__sbr_cell_35_16_end:
__sbr_cell_35_17:
    mov ecx, DWORD PTR [rbx+312112]
__sbr_cell_35_17_end:
__sbr_cell_35_18:
    test ecx, ecx
__sbr_cell_35_18_end:
__sbr_cell_35_19:
    je sbr_make_f_tablelim.L3fcc
__sbr_cell_35_19_end:
sbr_make_f_tablelim.L3f59:
__sbr_cell_35_20:
    lea edx, [rcx-7]
__sbr_cell_35_20_end:
__sbr_cell_35_21:
    cmp edx, 4294967290
__sbr_cell_35_21_end:
__sbr_cell_35_22:
    jb sbr_make_f_tablelim.L43e6
__sbr_cell_35_22_end:
sbr_make_f_tablelim.L3f65:
__sbr_cell_35_23:
    movzx edx, BYTE PTR [rbx+312116]
__sbr_cell_35_23_end:
__sbr_cell_35_24:
    add eax, edx
__sbr_cell_35_24_end:
__sbr_cell_35_25:
    mov WORD PTR [rbp-44], ax
__sbr_cell_35_25_end:
__sbr_cell_35_26:
    cmp ecx, 1
__sbr_cell_35_26_end:
__sbr_cell_35_27:
    je sbr_make_f_tablelim.L3fcc
__sbr_cell_35_27_end:
sbr_make_f_tablelim.L3f77:
__sbr_cell_35_28:
    movzx edx, BYTE PTR [rbx+312117]
__sbr_cell_35_28_end:
__sbr_cell_35_29:
    add eax, edx
__sbr_cell_35_29_end:
__sbr_cell_35_30:
    mov WORD PTR [rbp-42], ax
__sbr_cell_35_30_end:
__sbr_cell_35_31:
    cmp ecx, 2
__sbr_cell_35_31_end:
__sbr_cell_35_32:
    je sbr_make_f_tablelim.L3fcc
__sbr_cell_35_32_end:
sbr_make_f_tablelim.L3f89:
__sbr_cell_35_33:
    movzx edx, BYTE PTR [rbx+312118]
__sbr_cell_35_33_end:
__sbr_cell_35_34:
    add eax, edx
__sbr_cell_35_34_end:
__sbr_cell_35_35:
    mov WORD PTR [rbp-40], ax
__sbr_cell_35_35_end:
__sbr_cell_35_36:
    cmp ecx, 3
__sbr_cell_35_36_end:
__sbr_cell_35_37:
    je sbr_make_f_tablelim.L3fcc
__sbr_cell_35_37_end:
sbr_make_f_tablelim.L3f9b:
__sbr_cell_35_38:
    movzx edx, BYTE PTR [rbx+312119]
__sbr_cell_35_38_end:
__sbr_cell_35_39:
    add eax, edx
__sbr_cell_35_39_end:
__sbr_cell_35_40:
    mov WORD PTR [rbp-38], ax
__sbr_cell_35_40_end:
__sbr_cell_35_41:
    cmp ecx, 4
__sbr_cell_35_41_end:
__sbr_cell_35_42:
    je sbr_make_f_tablelim.L3fcc
__sbr_cell_35_42_end:
sbr_make_f_tablelim.L3fad:
__sbr_cell_35_43:
    movzx edx, BYTE PTR [rbx+312120]
__sbr_cell_35_43_end:
__sbr_cell_35_44:
    add eax, edx
__sbr_cell_35_44_end:
__sbr_cell_35_45:
    mov WORD PTR [rbp-36], ax
__sbr_cell_35_45_end:
__sbr_cell_35_46:
    cmp ecx, 5
__sbr_cell_35_46_end:
__sbr_cell_35_47:
    je sbr_make_f_tablelim.L3fcc
__sbr_cell_35_47_end:
sbr_make_f_tablelim.L3fbf:
__sbr_cell_35_48:
    movzx ecx, BYTE PTR [rbx+312121]
__sbr_cell_35_48_end:
__sbr_cell_35_49:
    add eax, ecx
__sbr_cell_35_49_end:
__sbr_cell_35_50:
    mov WORD PTR [rbp-34], ax
__sbr_cell_35_50_end:
sbr_make_f_tablelim.L3fcc:
__sbr_cell_35_51:
    vmovss DWORD PTR [rbp-52], xmm0
__sbr_cell_35_51_end:
__sbr_cell_35_52:
    lea r14, [rbx+312050]
__sbr_cell_35_52_end:
__sbr_cell_35_53:
    lea rsi, [rbx+311890]
__sbr_cell_35_53_end:
__sbr_cell_35_54:
    mov r15d, DWORD PTR [rbx+311776]
__sbr_cell_35_54_end:
__sbr_cell_35_55:
    lea edx, [r15+1]
__sbr_cell_35_55_end:
__sbr_cell_35_56:
    add rdx, rdx
__sbr_cell_35_56_end:
__sbr_cell_35_57:
    mov rdi, r14
__sbr_cell_35_57_end:
__sbr_cell_35_58:
    call memcpy
__sbr_cell_35_58_end:
sbr_make_f_tablelim.L3ff5:
__sbr_cell_35_59:
    mov edx, DWORD PTR [rbx+312112]
__sbr_cell_35_59_end:
__sbr_cell_35_60:
    cmp edx, 2
__sbr_cell_35_60_end:
__sbr_cell_35_61:
    jb sbr_make_f_tablelim.L4026
__sbr_cell_35_61_end:
sbr_make_f_tablelim.L4000:
__sbr_cell_35_62:
    cmp r15d, 31
__sbr_cell_35_62_end:
__sbr_cell_35_63:
    jae sbr_make_f_tablelim.L43f0
__sbr_cell_35_63_end:
sbr_make_f_tablelim.L400a:
__sbr_cell_35_64:
    lea rdi, [r14+r15*2+0]
__sbr_cell_35_64_end:
__sbr_cell_35_65:
    add rdi, 2
__sbr_cell_35_65_end:
__sbr_cell_35_66:
    lea rsi, [rbp-44]
__sbr_cell_35_66_end:
__sbr_cell_35_67:
    dec edx
__sbr_cell_35_67_end:
__sbr_cell_35_68:
    add rdx, rdx
__sbr_cell_35_68_end:
__sbr_cell_35_69:
    call memcpy
__sbr_cell_35_69_end:
sbr_make_f_tablelim.L4020:
__sbr_cell_35_70:
    mov edx, DWORD PTR [rbx+312112]
__sbr_cell_35_70_end:
sbr_make_f_tablelim.L4026:
__sbr_cell_35_71:
    mov QWORD PTR [rbp-1088], r14
__sbr_cell_35_71_end:
__sbr_cell_35_72:
    add r15d, edx
__sbr_cell_35_72_end:
__sbr_cell_35_73:
    cmp r15d, 31
__sbr_cell_35_73_end:
__sbr_cell_35_74:
    vmovss xmm2, DWORD PTR [rbp-52]
__sbr_cell_35_74_end:
__sbr_cell_35_75:
    jae sbr_make_f_tablelim.L43e1
__sbr_cell_35_75_end:
sbr_make_f_tablelim.L403f:
__sbr_cell_35_76:
    lea rax, [rbx+312052]
__sbr_cell_35_76_end:
__sbr_cell_35_77:
    mov ecx, r15d
__sbr_cell_35_77_end:
__sbr_cell_35_78:
    lea rcx, [r14+rcx*2+0]
__sbr_cell_35_78_end:
__sbr_cell_35_79:
    add rcx, -2
__sbr_cell_35_79_end:
__sbr_cell_35_80:
    mov QWORD PTR [rbp-1080], rcx
__sbr_cell_35_80_end:
__sbr_cell_35_81:
    mov ecx, 1
__sbr_cell_35_81_end:
__sbr_cell_35_82:
    jmp sbr_make_f_tablelim.L4068
__sbr_cell_35_82_end:
__sbr_cell_35_83:
    .nops 1
__sbr_cell_35_83_end:
sbr_make_f_tablelim.L4060:
__sbr_cell_35_84:
    test ecx, ecx
__sbr_cell_35_84_end:
__sbr_cell_35_85:
    je sbr_make_f_tablelim.L429d
__sbr_cell_35_85_end:
sbr_make_f_tablelim.L4068:
__sbr_cell_35_86:
    cmp ecx, 65
__sbr_cell_35_86_end:
__sbr_cell_35_87:
    jae sbr_make_f_tablelim.L43d7
__sbr_cell_35_87_end:
__sbr_cell_35_88:
    dec ecx
__sbr_cell_35_88_end:
__sbr_cell_35_89:
    mov rdx, rcx
__sbr_cell_35_89_end:
__sbr_cell_35_90:
    shl rdx, 4
__sbr_cell_35_90_end:
__sbr_cell_35_91:
    mov rsi, QWORD PTR [rbp+rdx*1-1088]
__sbr_cell_35_91_end:
__sbr_cell_35_92:
    mov rdx, QWORD PTR [rbp+rdx*1-1080]
__sbr_cell_35_92_end:
__sbr_cell_35_93:
    .nops 1
__sbr_cell_35_93_end:
sbr_make_f_tablelim.L4090:
__sbr_cell_35_94:
    cmp rsi, rdx
__sbr_cell_35_94_end:
__sbr_cell_35_95:
    jae sbr_make_f_tablelim.L4060
__sbr_cell_35_95_end:
__sbr_cell_35_96:
    lea r8, [rdx-2]
__sbr_cell_35_96_end:
__sbr_cell_35_97:
    cmp rsi, r8
__sbr_cell_35_97_end:
__sbr_cell_35_98:
    jae sbr_make_f_tablelim.L4280
__sbr_cell_35_98_end:
__sbr_cell_35_99:
    mov r9, rdx
__sbr_cell_35_99_end:
__sbr_cell_35_100:
    sub r9, rsi
__sbr_cell_35_100_end:
__sbr_cell_35_101:
    sar r9, 2
__sbr_cell_35_101_end:
__sbr_cell_35_102:
    lea rdi, [rsi+r9*2+0]
__sbr_cell_35_102_end:
__sbr_cell_35_103:
    movzx r10d, WORD PTR [rsi+0]
__sbr_cell_35_103_end:
__sbr_cell_35_104:
    movzx r11d, WORD PTR [rdx+0]
__sbr_cell_35_104_end:
__sbr_cell_35_105:
    movzx r9d, WORD PTR [rsi+r9*2+0]
__sbr_cell_35_105_end:
__sbr_cell_35_106:
    cmp r10w, r11w
__sbr_cell_35_106_end:
__sbr_cell_35_107:
    jle sbr_make_f_tablelim.L40e0
__sbr_cell_35_107_end:
sbr_make_f_tablelim.L40c3:
__sbr_cell_35_108:
    cmp r11w, r9w
__sbr_cell_35_108_end:
__sbr_cell_35_109:
    jg sbr_make_f_tablelim.L40ec
__sbr_cell_35_109_end:
sbr_make_f_tablelim.L40c9:
__sbr_cell_35_110:
    mov WORD PTR [rdx+0], r10w
__sbr_cell_35_110_end:
__sbr_cell_35_111:
    mov r9d, r11d
__sbr_cell_35_111_end:
__sbr_cell_35_112:
    jmp sbr_make_f_tablelim.L40f0
__sbr_cell_35_112_end:
__sbr_cell_35_113:
    .nops 1
__sbr_cell_35_113_end:
sbr_make_f_tablelim.L40e0:
__sbr_cell_35_114:
    mov r11d, 1
__sbr_cell_35_114_end:
__sbr_cell_35_115:
    cmp r10w, r9w
__sbr_cell_35_115_end:
__sbr_cell_35_116:
    jle sbr_make_f_tablelim.L40f7
__sbr_cell_35_116_end:
sbr_make_f_tablelim.L40ec:
__sbr_cell_35_117:
    mov WORD PTR [rdi+0], r10w
__sbr_cell_35_117_end:
sbr_make_f_tablelim.L40f0:
__sbr_cell_35_118:
    mov WORD PTR [rsi+0], r9w
__sbr_cell_35_118_end:
__sbr_cell_35_119:
    xor r11d, r11d
__sbr_cell_35_119_end:
sbr_make_f_tablelim.L40f7:
__sbr_cell_35_120:
    movzx r9d, WORD PTR [rdi+0]
__sbr_cell_35_120_end:
__sbr_cell_35_121:
    movzx r15d, WORD PTR [rdx+0]
__sbr_cell_35_121_end:
__sbr_cell_35_122:
    cmp r9w, r15w
__sbr_cell_35_122_end:
__sbr_cell_35_123:
    jle sbr_make_f_tablelim.L4120
__sbr_cell_35_123_end:
sbr_make_f_tablelim.L4105:
__sbr_cell_35_124:
    mov WORD PTR [rdx+0], r9w
__sbr_cell_35_124_end:
__sbr_cell_35_125:
    mov WORD PTR [rdi+0], r15w
__sbr_cell_35_125_end:
__sbr_cell_35_126:
    xor r11d, r11d
__sbr_cell_35_126_end:
sbr_make_f_tablelim.L4110:
__sbr_cell_35_127:
    lea r9, [rdx-4]
__sbr_cell_35_127_end:
__sbr_cell_35_128:
    cmp rsi, r9
__sbr_cell_35_128_end:
__sbr_cell_35_129:
    jne sbr_make_f_tablelim.L4130
__sbr_cell_35_129_end:
__sbr_cell_35_130:
    jmp sbr_make_f_tablelim.L4060
__sbr_cell_35_130_end:
__sbr_cell_35_131:
    .nops 1
__sbr_cell_35_131_end:
sbr_make_f_tablelim.L4120:
__sbr_cell_35_132:
    mov r15d, r9d
__sbr_cell_35_132_end:
__sbr_cell_35_133:
    lea r9, [rdx-4]
__sbr_cell_35_133_end:
__sbr_cell_35_134:
    cmp rsi, r9
__sbr_cell_35_134_end:
__sbr_cell_35_135:
    je sbr_make_f_tablelim.L4060
__sbr_cell_35_135_end:
sbr_make_f_tablelim.L4130:
__sbr_cell_35_136:
    lea r10, [rsi+2]
__sbr_cell_35_136_end:
__sbr_cell_35_137:
    movzx r12d, WORD PTR [r8+0]
__sbr_cell_35_137_end:
__sbr_cell_35_138:
    mov WORD PTR [rdi+0], r12w
__sbr_cell_35_138_end:
__sbr_cell_35_139:
    mov WORD PTR [r8+0], r15w
__sbr_cell_35_139_end:
__sbr_cell_35_140:
    cmp r10, r9
__sbr_cell_35_140_end:
__sbr_cell_35_141:
    jbe sbr_make_f_tablelim.L4169
__sbr_cell_35_141_end:
__sbr_cell_35_142:
    jmp sbr_make_f_tablelim.L41b4
__sbr_cell_35_142_end:
__sbr_cell_35_143:
    .nops 1
__sbr_cell_35_143_end:
sbr_make_f_tablelim.L4150:
__sbr_cell_35_144:
    movzx r15d, WORD PTR [r10+0]
__sbr_cell_35_144_end:
__sbr_cell_35_145:
    mov WORD PTR [r9+0], r15w
__sbr_cell_35_145_end:
__sbr_cell_35_146:
    mov WORD PTR [r10+0], r12w
__sbr_cell_35_146_end:
__sbr_cell_35_147:
    add r10, 2
__sbr_cell_35_147_end:
__sbr_cell_35_148:
    add r9, -2
__sbr_cell_35_148_end:
sbr_make_f_tablelim.L4164:
__sbr_cell_35_149:
    cmp r10, r9
__sbr_cell_35_149_end:
__sbr_cell_35_150:
    ja sbr_make_f_tablelim.L41b0
__sbr_cell_35_150_end:
sbr_make_f_tablelim.L4169:
__sbr_cell_35_151:
    movzx r15d, WORD PTR [r8+0]
__sbr_cell_35_151_end:
__sbr_cell_35_152:
    .nops 1
__sbr_cell_35_152_end:
sbr_make_f_tablelim.L4170:
__sbr_cell_35_153:
    cmp WORD PTR [r10+0], r15w
__sbr_cell_35_153_end:
__sbr_cell_35_154:
    jge sbr_make_f_tablelim.L4194
__sbr_cell_35_154_end:
__sbr_cell_35_155:
    add r10, 2
__sbr_cell_35_155_end:
__sbr_cell_35_156:
    cmp r10, r9
__sbr_cell_35_156_end:
__sbr_cell_35_157:
    jbe sbr_make_f_tablelim.L4170
__sbr_cell_35_157_end:
__sbr_cell_35_158:
    jmp sbr_make_f_tablelim.L4194
__sbr_cell_35_158_end:
__sbr_cell_35_159:
    .nops 1
__sbr_cell_35_159_end:
sbr_make_f_tablelim.L4190:
__sbr_cell_35_160:
    add r9, -2
__sbr_cell_35_160_end:
sbr_make_f_tablelim.L4194:
__sbr_cell_35_161:
    cmp r10, r9
__sbr_cell_35_161_end:
__sbr_cell_35_162:
    ja sbr_make_f_tablelim.L4164
__sbr_cell_35_162_end:
sbr_make_f_tablelim.L4199:
__sbr_cell_35_163:
    movzx r12d, WORD PTR [r9+0]
__sbr_cell_35_163_end:
__sbr_cell_35_164:
    cmp r12w, r15w
__sbr_cell_35_164_end:
__sbr_cell_35_165:
    jg sbr_make_f_tablelim.L4190
__sbr_cell_35_165_end:
__sbr_cell_35_166:
    jmp sbr_make_f_tablelim.L4150
__sbr_cell_35_166_end:
__sbr_cell_35_167:
    .nops 1
__sbr_cell_35_167_end:
sbr_make_f_tablelim.L41b0:
__sbr_cell_35_168:
    movzx r15d, WORD PTR [r8+0]
__sbr_cell_35_168_end:
sbr_make_f_tablelim.L41b4:
__sbr_cell_35_169:
    movzx r12d, WORD PTR [r10+0]
__sbr_cell_35_169_end:
__sbr_cell_35_170:
    mov WORD PTR [r10+0], r15w
__sbr_cell_35_170_end:
__sbr_cell_35_171:
    mov WORD PTR [r8+0], r12w
__sbr_cell_35_171_end:
__sbr_cell_35_172:
    test r11d, r11d
__sbr_cell_35_172_end:
__sbr_cell_35_173:
    je sbr_make_f_tablelim.L4200
__sbr_cell_35_173_end:
__sbr_cell_35_174:
    cmp rdi, r10
__sbr_cell_35_174_end:
__sbr_cell_35_175:
    je sbr_make_f_tablelim.L41d3
__sbr_cell_35_175_end:
sbr_make_f_tablelim.L41ca:
__sbr_cell_35_176:
    lea r8, [r10-2]
__sbr_cell_35_176_end:
__sbr_cell_35_177:
    cmp rdi, r8
__sbr_cell_35_177_end:
__sbr_cell_35_178:
    jne sbr_make_f_tablelim.L4200
__sbr_cell_35_178_end:
sbr_make_f_tablelim.L41d3:
__sbr_cell_35_179:
    mov r8, rsi
__sbr_cell_35_179_end:
__sbr_cell_35_180:
    .nops 1
__sbr_cell_35_180_end:
sbr_make_f_tablelim.L41e0:
__sbr_cell_35_181:
    mov rdi, r8
__sbr_cell_35_181_end:
__sbr_cell_35_182:
    cmp r8, rdx
__sbr_cell_35_182_end:
__sbr_cell_35_183:
    jae sbr_make_f_tablelim.L41f7
__sbr_cell_35_183_end:
__sbr_cell_35_184:
    lea r8, [rdi+2]
__sbr_cell_35_184_end:
__sbr_cell_35_185:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_35_185_end:
__sbr_cell_35_186:
    cmp r11w, WORD PTR [rdi+2]
__sbr_cell_35_186_end:
__sbr_cell_35_187:
    jle sbr_make_f_tablelim.L41e0
__sbr_cell_35_187_end:
sbr_make_f_tablelim.L41f7:
__sbr_cell_35_188:
    cmp rdi, rdx
__sbr_cell_35_188_end:
__sbr_cell_35_189:
    je sbr_make_f_tablelim.L4060
__sbr_cell_35_189_end:
sbr_make_f_tablelim.L4200:
__sbr_cell_35_190:
    mov rdi, rdx
__sbr_cell_35_190_end:
__sbr_cell_35_191:
    sub rdi, r10
__sbr_cell_35_191_end:
__sbr_cell_35_192:
    mov r8, r10
__sbr_cell_35_192_end:
__sbr_cell_35_193:
    sub r8, rsi
__sbr_cell_35_193_end:
__sbr_cell_35_194:
    cmp rdi, r8
__sbr_cell_35_194_end:
__sbr_cell_35_195:
    jge sbr_make_f_tablelim.L4250
__sbr_cell_35_195_end:
sbr_make_f_tablelim.L4211:
__sbr_cell_35_196:
    cmp rcx, 64
__sbr_cell_35_196_end:
__sbr_cell_35_197:
    jae sbr_make_f_tablelim.L43cd
__sbr_cell_35_197_end:
sbr_make_f_tablelim.L421b:
__sbr_cell_35_198:
    mov rdi, rcx
__sbr_cell_35_198_end:
__sbr_cell_35_199:
    shl rdi, 4
__sbr_cell_35_199_end:
__sbr_cell_35_200:
    mov QWORD PTR [rbp+rdi*1-1088], rsi
__sbr_cell_35_200_end:
__sbr_cell_35_201:
    mov QWORD PTR [rbp+rdi*1-1080], r9
__sbr_cell_35_201_end:
__sbr_cell_35_202:
    add r10, 2
__sbr_cell_35_202_end:
__sbr_cell_35_203:
    mov rsi, r10
__sbr_cell_35_203_end:
__sbr_cell_35_204:
    inc rcx
__sbr_cell_35_204_end:
__sbr_cell_35_205:
    jmp sbr_make_f_tablelim.L4090
__sbr_cell_35_205_end:
__sbr_cell_35_206:
    .nops 1
__sbr_cell_35_206_end:
sbr_make_f_tablelim.L4250:
__sbr_cell_35_207:
    cmp rcx, 64
__sbr_cell_35_207_end:
__sbr_cell_35_208:
    jae sbr_make_f_tablelim.L43d2
__sbr_cell_35_208_end:
sbr_make_f_tablelim.L425a:
__sbr_cell_35_209:
    add r10, 2
__sbr_cell_35_209_end:
__sbr_cell_35_210:
    mov rdi, rcx
__sbr_cell_35_210_end:
__sbr_cell_35_211:
    shl rdi, 4
__sbr_cell_35_211_end:
__sbr_cell_35_212:
    mov QWORD PTR [rbp+rdi*1-1088], r10
__sbr_cell_35_212_end:
__sbr_cell_35_213:
    mov QWORD PTR [rbp+rdi*1-1080], rdx
__sbr_cell_35_213_end:
__sbr_cell_35_214:
    mov rdx, r9
__sbr_cell_35_214_end:
__sbr_cell_35_215:
    inc rcx
__sbr_cell_35_215_end:
__sbr_cell_35_216:
    jmp sbr_make_f_tablelim.L4090
__sbr_cell_35_216_end:
sbr_make_f_tablelim.L4280:
__sbr_cell_35_217:
    movzx edi, WORD PTR [rsi+0]
__sbr_cell_35_217_end:
__sbr_cell_35_218:
    movzx r8d, WORD PTR [rdx+0]
__sbr_cell_35_218_end:
__sbr_cell_35_219:
    cmp di, r8w
__sbr_cell_35_219_end:
__sbr_cell_35_220:
    jle sbr_make_f_tablelim.L4060
__sbr_cell_35_220_end:
__sbr_cell_35_221:
    mov WORD PTR [rdx+0], di
__sbr_cell_35_221_end:
__sbr_cell_35_222:
    mov WORD PTR [rsi+0], r8w
__sbr_cell_35_222_end:
__sbr_cell_35_223:
    jmp sbr_make_f_tablelim.L4060
__sbr_cell_35_223_end:
sbr_make_f_tablelim.L429d:
__sbr_cell_35_224:
    mov ecx, DWORD PTR [rbx+311776]
__sbr_cell_35_224_end:
__sbr_cell_35_225:
    mov edx, DWORD PTR [rbx+312112]
__sbr_cell_35_225_end:
__sbr_cell_35_226:
    add edx, ecx
__sbr_cell_35_226_end:
__sbr_cell_35_227:
    dec edx
__sbr_cell_35_227_end:
__sbr_cell_35_228:
    mov DWORD PTR [rbx+311788], edx
__sbr_cell_35_228_end:
__sbr_cell_35_229:
    cmp edx, 30
__sbr_cell_35_229_end:
sbr_make_f_tablelim.L42b6:
__sbr_cell_35_230:
    ja sbr_make_f_tablelim.L4385
__sbr_cell_35_230_end:
sbr_make_f_tablelim.L42bc:
__sbr_cell_35_231:
    mov rcx, r14
__sbr_cell_35_231_end:
__sbr_cell_35_232:
    jmp sbr_make_f_tablelim.L42eb
__sbr_cell_35_232_end:
__sbr_cell_35_233:
    .nops 1
__sbr_cell_35_233_end:
sbr_make_f_tablelim.L42d0:
__sbr_cell_35_234:
    mov WORD PTR [rcx+2], si
__sbr_cell_35_234_end:
__sbr_cell_35_235:
    add rcx, 2
__sbr_cell_35_235_end:
__sbr_cell_35_236:
    mov edx, DWORD PTR [rbx+311788]
__sbr_cell_35_236_end:
__sbr_cell_35_237:
    add rax, 2
__sbr_cell_35_237_end:
__sbr_cell_35_238:
    cmp edx, 31
__sbr_cell_35_238_end:
__sbr_cell_35_239:
    jae sbr_make_f_tablelim.L4385
__sbr_cell_35_239_end:
sbr_make_f_tablelim.L42eb:
__sbr_cell_35_240:
    mov esi, edx
__sbr_cell_35_240_end:
__sbr_cell_35_241:
    lea rsi, [r14+rsi*2+0]
__sbr_cell_35_241_end:
__sbr_cell_35_242:
    cmp rcx, rsi
__sbr_cell_35_242_end:
__sbr_cell_35_243:
    jae sbr_make_f_tablelim.L43bd
__sbr_cell_35_243_end:
sbr_make_f_tablelim.L42fa:
__sbr_cell_35_244:
    movzx esi, WORD PTR [rax+0]
__sbr_cell_35_244_end:
__sbr_cell_35_245:
    vcvtsi2ss xmm0, xmm15, esi
__sbr_cell_35_245_end:
__sbr_cell_35_246:
    movzx edi, WORD PTR [rcx+0]
__sbr_cell_35_246_end:
__sbr_cell_35_247:
    vcvtsi2ss xmm1, xmm15, edi
__sbr_cell_35_247_end:
__sbr_cell_35_248:
    vmulss xmm1, xmm2, xmm1
__sbr_cell_35_248_end:
__sbr_cell_35_249:
    vucomiss xmm0, xmm1
__sbr_cell_35_249_end:
__sbr_cell_35_250:
    jae sbr_make_f_tablelim.L42d0
__sbr_cell_35_250_end:
sbr_make_f_tablelim.L4312:
__sbr_cell_35_251:
    cmp si, di
__sbr_cell_35_251_end:
__sbr_cell_35_252:
    je sbr_make_f_tablelim.L4370
__sbr_cell_35_252_end:
sbr_make_f_tablelim.L4317:
__sbr_cell_35_253:
    mov r8d, DWORD PTR [rbx+312112]
__sbr_cell_35_253_end:
__sbr_cell_35_254:
    test r8d, r8d
__sbr_cell_35_254_end:
__sbr_cell_35_255:
    js sbr_make_f_tablelim.L4370
__sbr_cell_35_255_end:
sbr_make_f_tablelim.L4323:
__sbr_cell_35_256:
    inc r8
__sbr_cell_35_256_end:
__sbr_cell_35_257:
    xor r9d, r9d
__sbr_cell_35_257_end:
__sbr_cell_35_258:
    .nops 1
__sbr_cell_35_258_end:
sbr_make_f_tablelim.L4330:
__sbr_cell_35_259:
    cmp WORD PTR [rbp+r9*2-46], si
__sbr_cell_35_259_end:
__sbr_cell_35_260:
    je sbr_make_f_tablelim.L4342
__sbr_cell_35_260_end:
sbr_make_f_tablelim.L4338:
__sbr_cell_35_261:
    inc r9
__sbr_cell_35_261_end:
__sbr_cell_35_262:
    cmp r8, r9
__sbr_cell_35_262_end:
__sbr_cell_35_263:
    jne sbr_make_f_tablelim.L4330
__sbr_cell_35_263_end:
sbr_make_f_tablelim.L4340:
__sbr_cell_35_264:
    jmp sbr_make_f_tablelim.L4370
__sbr_cell_35_264_end:
sbr_make_f_tablelim.L4342:
__sbr_cell_35_265:
    xor edx, edx
__sbr_cell_35_265_end:
__sbr_cell_35_266:
    .nops 1
__sbr_cell_35_266_end:
sbr_make_f_tablelim.L4350:
__sbr_cell_35_267:
    cmp WORD PTR [rbp+rdx*2-46], di
__sbr_cell_35_267_end:
__sbr_cell_35_268:
    je sbr_make_f_tablelim.L42d0
__sbr_cell_35_268_end:
sbr_make_f_tablelim.L435b:
__sbr_cell_35_269:
    inc rdx
__sbr_cell_35_269_end:
__sbr_cell_35_270:
    cmp r8, rdx
__sbr_cell_35_270_end:
__sbr_cell_35_271:
    jne sbr_make_f_tablelim.L4350
__sbr_cell_35_271_end:
sbr_make_f_tablelim.L4363:
__sbr_cell_35_272:
    mov WORD PTR [rcx+0], si
__sbr_cell_35_272_end:
__sbr_cell_35_273:
    mov edx, DWORD PTR [rbx+311788]
__sbr_cell_35_273_end:
__sbr_cell_35_274:
    .nops 1
__sbr_cell_35_274_end:
sbr_make_f_tablelim.L4370:
__sbr_cell_35_275:
    dec edx
__sbr_cell_35_275_end:
__sbr_cell_35_276:
    mov DWORD PTR [rbx+311788], edx
__sbr_cell_35_276_end:
__sbr_cell_35_277:
    add rax, 2
__sbr_cell_35_277_end:
__sbr_cell_35_278:
    cmp edx, 31
__sbr_cell_35_278_end:
__sbr_cell_35_279:
    jb sbr_make_f_tablelim.L42eb
__sbr_cell_35_279_end:
sbr_make_f_tablelim.L4385:
__sbr_cell_35_280:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_280_end:
sbr_make_f_tablelim.L438a:
__sbr_cell_35_281:
    movzx eax, WORD PTR [rbx+311890]
__sbr_cell_35_281_end:
__sbr_cell_35_282:
    mov WORD PTR [rbx+312050], ax
__sbr_cell_35_282_end:
sbr_make_f_tablelim.L4398:
__sbr_cell_35_283:
    mov eax, DWORD PTR [rbx+311776]
__sbr_cell_35_283_end:
__sbr_cell_35_284:
    cmp rax, 25
__sbr_cell_35_284_end:
__sbr_cell_35_285:
    jae sbr_make_f_tablelim.L43eb
__sbr_cell_35_285_end:
sbr_make_f_tablelim.L43a4:
__sbr_cell_35_286:
    movzx eax, WORD PTR [rbx+rax*2+311890]
__sbr_cell_35_286_end:
__sbr_cell_35_287:
    mov WORD PTR [rbx+312052], ax
__sbr_cell_35_287_end:
__sbr_cell_35_288:
    mov DWORD PTR [rbx+311788], 1
__sbr_cell_35_288_end:
sbr_make_f_tablelim.L43bd:
__sbr_cell_35_289:
    add rsp, 1056
__sbr_cell_35_289_end:
__sbr_cell_35_290:
    pop rbx
__sbr_cell_35_290_end:
__sbr_cell_35_291:
    pop r12
__sbr_cell_35_291_end:
__sbr_cell_35_292:
    pop r14
__sbr_cell_35_292_end:
__sbr_cell_35_293:
    pop r15
__sbr_cell_35_293_end:
__sbr_cell_35_294:
    pop rbp
__sbr_cell_35_294_end:
sbr_make_f_tablelim.done:
__sbr_cell_35_295:
    ret
__sbr_cell_35_295_end:
sbr_make_f_tablelim.L43cd:
__sbr_cell_35_296:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_296_end:
sbr_make_f_tablelim.L43d2:
__sbr_cell_35_297:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_297_end:
sbr_make_f_tablelim.L43d7:
__sbr_cell_35_298:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_298_end:
sbr_make_f_tablelim.L43dc:
__sbr_cell_35_299:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_299_end:
sbr_make_f_tablelim.L43e1:
__sbr_cell_35_300:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_300_end:
sbr_make_f_tablelim.L43e6:
__sbr_cell_35_301:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_301_end:
sbr_make_f_tablelim.L43eb:
__sbr_cell_35_302:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_302_end:
sbr_make_f_tablelim.L43f0:
__sbr_cell_35_303:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_35_303_end:
__sbr_cell_35_304:
    int3
__sbr_cell_35_304_end:
__sbr_cell_35_305:
    int3
__sbr_cell_35_305_end:
__sbr_cell_35_306:
    int3
__sbr_cell_35_306_end:
__sbr_cell_35_307:
    int3
__sbr_cell_35_307_end:
__sbr_cell_35_308:
    int3
__sbr_cell_35_308_end:
__sbr_cell_35_309:
    int3
__sbr_cell_35_309_end:
__sbr_cell_35_310:
    int3
__sbr_cell_35_310_end:
__sbr_cell_35_311:
    int3
__sbr_cell_35_311_end:
__sbr_cell_35_312:
    int3
__sbr_cell_35_312_end:
__sbr_cell_35_313:
    int3
__sbr_cell_35_313_end:
__sbr_cell_35_314:
    int3
__sbr_cell_35_314_end:
.size sbr_make_f_tablelim, .-sbr_make_f_tablelim
.section .text.sbr_qmf_synthesis,"ax",@progbits
.globl sbr_qmf_synthesis
.type sbr_qmf_synthesis,@function
sbr_qmf_synthesis:
__sbr_cell_36_0:
    push rbp
__sbr_cell_36_0_end:
__sbr_cell_36_1:
    mov rbp, rsp
__sbr_cell_36_1_end:
__sbr_cell_36_2:
    push r15
__sbr_cell_36_2_end:
__sbr_cell_36_3:
    push r14
__sbr_cell_36_3_end:
__sbr_cell_36_4:
    push r13
__sbr_cell_36_4_end:
__sbr_cell_36_5:
    push r12
__sbr_cell_36_5_end:
__sbr_cell_36_6:
    push rbx
__sbr_cell_36_6_end:
__sbr_cell_36_7:
    sub rsp, 248
__sbr_cell_36_7_end:
sbr_qmf_synthesis.e1:
__sbr_cell_36_8:
    mov rbx, r9
__sbr_cell_36_8_end:
__sbr_cell_36_9:
    mov r14, r8
__sbr_cell_36_9_end:
__sbr_cell_36_10:
    mov QWORD PTR [rbp-280], rcx
__sbr_cell_36_10_end:
__sbr_cell_36_11:
    mov QWORD PTR [rbp-48], rdx
__sbr_cell_36_11_end:
__sbr_cell_36_12:
    mov QWORD PTR [rbp-64], rsi
__sbr_cell_36_12_end:
__sbr_cell_36_13:
    mov QWORD PTR [rbp-56], rdi
__sbr_cell_36_13_end:
__sbr_cell_36_14:
    lea rax, [rip+_GLOBAL_OFFSET_TABLE_]
__sbr_cell_36_14_end:
__sbr_cell_36_15:
    mov ecx, DWORD PTR [rbp+40]
__sbr_cell_36_15_end:
__sbr_cell_36_16:
    movabs rdx, offset sbr_qmf_window_ds@GOTOFF
__sbr_cell_36_16_end:
__sbr_cell_36_17:
    add rdx, rax
__sbr_cell_36_17_end:
__sbr_cell_36_18:
    movabs rsi, offset sbr_qmf_window_us@GOTOFF
__sbr_cell_36_18_end:
__sbr_cell_36_19:
    add rsi, rax
__sbr_cell_36_19_end:
__sbr_cell_36_20:
    test ecx, ecx
__sbr_cell_36_20_end:
__sbr_cell_36_21:
    cmovne rsi, rdx
__sbr_cell_36_21_end:
sbr_qmf_synthesis.e2:
__sbr_cell_36_22:
    mov r13d, 128
__sbr_cell_36_22_end:
__sbr_cell_36_23:
    shr r13d, cl
__sbr_cell_36_23_end:
__sbr_cell_36_24:
    mov eax, 1152
__sbr_cell_36_24_end:
__sbr_cell_36_25:
    shr eax, cl
__sbr_cell_36_25_end:
__sbr_cell_36_26:
    mov edi, 2304
__sbr_cell_36_26_end:
__sbr_cell_36_27:
    sub edi, eax
__sbr_cell_36_27_end:
__sbr_cell_36_28:
    shl eax, 2
__sbr_cell_36_28_end:
__sbr_cell_36_29:
    mov QWORD PTR [rbp-96], rax
__sbr_cell_36_29_end:
__sbr_cell_36_30:
    mov r8d, 64
__sbr_cell_36_30_end:
__sbr_cell_36_31:
    shr r8d, cl
__sbr_cell_36_31_end:
__sbr_cell_36_32:
    mov r9d, 192
__sbr_cell_36_32_end:
__sbr_cell_36_33:
    shr r9d, cl
__sbr_cell_36_33_end:
__sbr_cell_36_34:
    mov r10d, 256
__sbr_cell_36_34_end:
__sbr_cell_36_35:
    shr r10d, cl
__sbr_cell_36_35_end:
__sbr_cell_36_36:
    mov r11d, 448
__sbr_cell_36_36_end:
__sbr_cell_36_37:
    shr r11d, cl
__sbr_cell_36_37_end:
__sbr_cell_36_38:
    mov r12d, 512
__sbr_cell_36_38_end:
__sbr_cell_36_39:
    shr r12d, cl
__sbr_cell_36_39_end:
sbr_qmf_synthesis.e3:
__sbr_cell_36_40:
    mov eax, 704
__sbr_cell_36_40_end:
__sbr_cell_36_41:
    shr eax, cl
__sbr_cell_36_41_end:
__sbr_cell_36_42:
    mov QWORD PTR [rbp-216], rax
__sbr_cell_36_42_end:
__sbr_cell_36_43:
    mov eax, 320
__sbr_cell_36_43_end:
__sbr_cell_36_44:
    shr eax, cl
__sbr_cell_36_44_end:
__sbr_cell_36_45:
    lea rax, [rsi+rax*4+0]
__sbr_cell_36_45_end:
__sbr_cell_36_46:
    mov QWORD PTR [rbp-208], rax
__sbr_cell_36_46_end:
__sbr_cell_36_47:
    mov eax, 768
__sbr_cell_36_47_end:
__sbr_cell_36_48:
    shr eax, cl
__sbr_cell_36_48_end:
__sbr_cell_36_49:
    mov QWORD PTR [rbp-200], rax
__sbr_cell_36_49_end:
__sbr_cell_36_50:
    mov eax, 384
__sbr_cell_36_50_end:
__sbr_cell_36_51:
    shr eax, cl
__sbr_cell_36_51_end:
__sbr_cell_36_52:
    mov edx, 960
__sbr_cell_36_52_end:
__sbr_cell_36_53:
    shr edx, cl
__sbr_cell_36_53_end:
__sbr_cell_36_54:
    mov QWORD PTR [rbp-192], rdx
__sbr_cell_36_54_end:
sbr_qmf_synthesis.e4:
__sbr_cell_36_55:
    mov edx, 1024
__sbr_cell_36_55_end:
__sbr_cell_36_56:
    shr edx, cl
__sbr_cell_36_56_end:
__sbr_cell_36_57:
    mov QWORD PTR [rbp-184], rdx
__sbr_cell_36_57_end:
__sbr_cell_36_58:
    mov edx, 1216
__sbr_cell_36_58_end:
__sbr_cell_36_59:
    shr edx, cl
__sbr_cell_36_59_end:
__sbr_cell_36_60:
    mov QWORD PTR [rbp-176], rdx
__sbr_cell_36_60_end:
__sbr_cell_36_61:
    mov edx, 576
__sbr_cell_36_61_end:
__sbr_cell_36_62:
    shr edx, cl
__sbr_cell_36_62_end:
__sbr_cell_36_63:
    lea rax, [rsi+rax*4+0]
__sbr_cell_36_63_end:
__sbr_cell_36_64:
    mov QWORD PTR [rbp-168], rax
__sbr_cell_36_64_end:
__sbr_cell_36_65:
    lea rax, [rsi+rdx*4+0]
__sbr_cell_36_65_end:
__sbr_cell_36_66:
    mov QWORD PTR [rbp-160], rax
__sbr_cell_36_66_end:
sbr_qmf_synthesis.e5:
__sbr_cell_36_67:
    mov rax, QWORD PTR [rbp+24]
__sbr_cell_36_67_end:
__sbr_cell_36_68:
    mov rcx, QWORD PTR [rbp+16]
__sbr_cell_36_68_end:
__sbr_cell_36_69:
    mov QWORD PTR [rbp-88], rdi
__sbr_cell_36_69_end:
__sbr_cell_36_70:
    lea rax, [rax+rdi*4+0]
__sbr_cell_36_70_end:
__sbr_cell_36_71:
    mov QWORD PTR [rbp-80], rax
__sbr_cell_36_71_end:
__sbr_cell_36_72:
    lea rax, [rcx+256]
__sbr_cell_36_72_end:
__sbr_cell_36_73:
    mov QWORD PTR [rbp-72], rax
__sbr_cell_36_73_end:
__sbr_cell_36_74:
    mov QWORD PTR [rbp-256], r8
__sbr_cell_36_74_end:
sbr_qmf_synthesis.e6:
__sbr_cell_36_75:
    lea eax, [r8*4+0]
__sbr_cell_36_75_end:
__sbr_cell_36_76:
    mov QWORD PTR [rbp-152], rax
__sbr_cell_36_76_end:
__sbr_cell_36_77:
    lea rax, [rsi+rax*1+0]
__sbr_cell_36_77_end:
__sbr_cell_36_78:
    mov QWORD PTR [rbp-144], rax
__sbr_cell_36_78_end:
__sbr_cell_36_79:
    lea rax, [rsi+r13*4+0]
__sbr_cell_36_79_end:
__sbr_cell_36_80:
    mov QWORD PTR [rbp-136], rax
__sbr_cell_36_80_end:
__sbr_cell_36_81:
    mov QWORD PTR [rbp-248], r9
__sbr_cell_36_81_end:
__sbr_cell_36_82:
    lea rax, [rsi+r9*4+0]
__sbr_cell_36_82_end:
__sbr_cell_36_83:
    mov QWORD PTR [rbp-128], rax
__sbr_cell_36_83_end:
__sbr_cell_36_84:
    mov QWORD PTR [rbp-240], r10
__sbr_cell_36_84_end:
__sbr_cell_36_85:
    lea rax, [rsi+r10*4+0]
__sbr_cell_36_85_end:
__sbr_cell_36_86:
    mov QWORD PTR [rbp-120], rax
__sbr_cell_36_86_end:
__sbr_cell_36_87:
    mov QWORD PTR [rbp-232], r11
__sbr_cell_36_87_end:
sbr_qmf_synthesis.e7:
__sbr_cell_36_88:
    lea rax, [rsi+r11*4+0]
__sbr_cell_36_88_end:
__sbr_cell_36_89:
    mov QWORD PTR [rbp-112], rax
__sbr_cell_36_89_end:
__sbr_cell_36_90:
    mov QWORD PTR [rbp-272], rsi
__sbr_cell_36_90_end:
__sbr_cell_36_91:
    mov QWORD PTR [rbp-224], r12
__sbr_cell_36_91_end:
__sbr_cell_36_92:
    lea rax, [rsi+r12*4+0]
__sbr_cell_36_92_end:
__sbr_cell_36_93:
    mov QWORD PTR [rbp-104], rax
__sbr_cell_36_93_end:
__sbr_cell_36_94:
    mov eax, 32
__sbr_cell_36_94_end:
__sbr_cell_36_95:
    mov QWORD PTR [rbp-264], r13
__sbr_cell_36_95_end:
__sbr_cell_36_96:
    jmp sbr_qmf_synthesis.L9fd2
__sbr_cell_36_96_end:
__sbr_cell_36_97:
    .nops 1
__sbr_cell_36_97_end:
sbr_qmf_synthesis.L9df0:
__sbr_cell_36_98:
    lea rdi, [rbx+9728]
__sbr_cell_36_98_end:
__sbr_cell_36_99:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_36_99_end:
__sbr_cell_36_100:
    call QWORD PTR [rax+16]
__sbr_cell_36_100_end:
sbr_qmf_synthesis.c1:
__sbr_cell_36_101:
    mov ecx, 4
__sbr_cell_36_101_end:
__sbr_cell_36_102:
    mov r12, QWORD PTR [rbp-56]
__sbr_cell_36_102_end:
__sbr_cell_36_103:
    mov rdi, r12
__sbr_cell_36_103_end:
__sbr_cell_36_104:
    mov rsi, QWORD PTR [rbp+16]
__sbr_cell_36_104_end:
__sbr_cell_36_105:
    mov rdx, rbx
__sbr_cell_36_105_end:
__sbr_cell_36_106:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_36_106_end:
__sbr_cell_36_107:
    call r15
__sbr_cell_36_107_end:
sbr_qmf_synthesis.c2:
__sbr_cell_36_108:
    mov ecx, 4
__sbr_cell_36_108_end:
__sbr_cell_36_109:
    mov rdi, r12
__sbr_cell_36_109_end:
__sbr_cell_36_110:
    mov r12, QWORD PTR [rbp-72]
__sbr_cell_36_110_end:
__sbr_cell_36_111:
    mov rsi, r12
__sbr_cell_36_111_end:
__sbr_cell_36_112:
    lea rdx, [rbx+9728]
__sbr_cell_36_112_end:
__sbr_cell_36_113:
    call r15
__sbr_cell_36_113_end:
sbr_qmf_synthesis.c3:
__sbr_cell_36_114:
    mov rdi, r13
__sbr_cell_36_114_end:
__sbr_cell_36_115:
    mov rsi, r12
__sbr_cell_36_115_end:
__sbr_cell_36_116:
    mov rdx, QWORD PTR [rbp+16]
__sbr_cell_36_116_end:
__sbr_cell_36_117:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_36_117_end:
__sbr_cell_36_118:
    call QWORD PTR [rax+48]
__sbr_cell_36_118_end:
sbr_qmf_synthesis.L9e42:
__sbr_cell_36_119:
    mov rdi, r14
__sbr_cell_36_119_end:
__sbr_cell_36_120:
    mov rsi, r13
__sbr_cell_36_120_end:
__sbr_cell_36_121:
    mov rdx, QWORD PTR [rbp-272]
__sbr_cell_36_121_end:
__sbr_cell_36_122:
    mov r12, QWORD PTR [rbp-256]
__sbr_cell_36_122_end:
__sbr_cell_36_123:
    mov ecx, r12d
__sbr_cell_36_123_end:
__sbr_cell_36_124:
    mov r15, QWORD PTR [rbp-280]
__sbr_cell_36_124_end:
__sbr_cell_36_125:
    call QWORD PTR [r15+0]
__sbr_cell_36_125_end:
sbr_qmf_synthesis.f1:
__sbr_cell_36_126:
    mov rax, QWORD PTR [rbp-248]
__sbr_cell_36_126_end:
__sbr_cell_36_127:
    lea rsi, [rax*4+0]
__sbr_cell_36_127_end:
__sbr_cell_36_128:
    add rsi, r13
__sbr_cell_36_128_end:
__sbr_cell_36_129:
    mov rdi, r14
__sbr_cell_36_129_end:
__sbr_cell_36_130:
    mov rdx, QWORD PTR [rbp-144]
__sbr_cell_36_130_end:
__sbr_cell_36_131:
    mov rcx, r14
__sbr_cell_36_131_end:
__sbr_cell_36_132:
    mov r8d, r12d
__sbr_cell_36_132_end:
__sbr_cell_36_133:
    call QWORD PTR [r15+48]
__sbr_cell_36_133_end:
sbr_qmf_synthesis.f2:
__sbr_cell_36_134:
    mov rax, QWORD PTR [rbp-240]
__sbr_cell_36_134_end:
__sbr_cell_36_135:
    lea rsi, [rax*4+0]
__sbr_cell_36_135_end:
__sbr_cell_36_136:
    add rsi, r13
__sbr_cell_36_136_end:
__sbr_cell_36_137:
    mov rdi, r14
__sbr_cell_36_137_end:
__sbr_cell_36_138:
    mov rdx, QWORD PTR [rbp-136]
__sbr_cell_36_138_end:
__sbr_cell_36_139:
    mov rcx, r14
__sbr_cell_36_139_end:
__sbr_cell_36_140:
    mov r8d, r12d
__sbr_cell_36_140_end:
__sbr_cell_36_141:
    call QWORD PTR [r15+48]
__sbr_cell_36_141_end:
sbr_qmf_synthesis.f3:
__sbr_cell_36_142:
    mov rax, QWORD PTR [rbp-232]
__sbr_cell_36_142_end:
__sbr_cell_36_143:
    lea rsi, [rax*4+0]
__sbr_cell_36_143_end:
__sbr_cell_36_144:
    add rsi, r13
__sbr_cell_36_144_end:
__sbr_cell_36_145:
    mov rdi, r14
__sbr_cell_36_145_end:
__sbr_cell_36_146:
    mov rdx, QWORD PTR [rbp-128]
__sbr_cell_36_146_end:
__sbr_cell_36_147:
    mov rcx, r14
__sbr_cell_36_147_end:
__sbr_cell_36_148:
    mov r8d, r12d
__sbr_cell_36_148_end:
__sbr_cell_36_149:
    call QWORD PTR [r15+48]
__sbr_cell_36_149_end:
sbr_qmf_synthesis.f4:
__sbr_cell_36_150:
    mov rax, QWORD PTR [rbp-224]
__sbr_cell_36_150_end:
__sbr_cell_36_151:
    lea rsi, [rax*4+0]
__sbr_cell_36_151_end:
__sbr_cell_36_152:
    add rsi, r13
__sbr_cell_36_152_end:
__sbr_cell_36_153:
    mov rdi, r14
__sbr_cell_36_153_end:
__sbr_cell_36_154:
    mov rdx, QWORD PTR [rbp-120]
__sbr_cell_36_154_end:
__sbr_cell_36_155:
    mov rcx, r14
__sbr_cell_36_155_end:
__sbr_cell_36_156:
    mov r8d, r12d
__sbr_cell_36_156_end:
__sbr_cell_36_157:
    call QWORD PTR [r15+48]
__sbr_cell_36_157_end:
sbr_qmf_synthesis.f5:
__sbr_cell_36_158:
    mov rax, QWORD PTR [rbp-216]
__sbr_cell_36_158_end:
__sbr_cell_36_159:
    lea rsi, [rax*4+0]
__sbr_cell_36_159_end:
__sbr_cell_36_160:
    add rsi, r13
__sbr_cell_36_160_end:
__sbr_cell_36_161:
    mov rdi, r14
__sbr_cell_36_161_end:
__sbr_cell_36_162:
    mov rdx, QWORD PTR [rbp-208]
__sbr_cell_36_162_end:
__sbr_cell_36_163:
    mov rcx, r14
__sbr_cell_36_163_end:
__sbr_cell_36_164:
    mov r8d, r12d
__sbr_cell_36_164_end:
__sbr_cell_36_165:
    call QWORD PTR [r15+48]
__sbr_cell_36_165_end:
sbr_qmf_synthesis.f6:
__sbr_cell_36_166:
    mov rax, QWORD PTR [rbp-200]
__sbr_cell_36_166_end:
__sbr_cell_36_167:
    lea rsi, [rax*4+0]
__sbr_cell_36_167_end:
__sbr_cell_36_168:
    add rsi, r13
__sbr_cell_36_168_end:
__sbr_cell_36_169:
    mov rdi, r14
__sbr_cell_36_169_end:
__sbr_cell_36_170:
    mov rdx, QWORD PTR [rbp-168]
__sbr_cell_36_170_end:
__sbr_cell_36_171:
    mov rcx, r14
__sbr_cell_36_171_end:
__sbr_cell_36_172:
    mov r8d, r12d
__sbr_cell_36_172_end:
__sbr_cell_36_173:
    call QWORD PTR [r15+48]
__sbr_cell_36_173_end:
sbr_qmf_synthesis.f7:
__sbr_cell_36_174:
    mov rax, QWORD PTR [rbp-192]
__sbr_cell_36_174_end:
__sbr_cell_36_175:
    lea rsi, [rax*4+0]
__sbr_cell_36_175_end:
__sbr_cell_36_176:
    add rsi, r13
__sbr_cell_36_176_end:
__sbr_cell_36_177:
    mov rdi, r14
__sbr_cell_36_177_end:
__sbr_cell_36_178:
    mov rdx, QWORD PTR [rbp-112]
__sbr_cell_36_178_end:
__sbr_cell_36_179:
    mov rcx, r14
__sbr_cell_36_179_end:
__sbr_cell_36_180:
    mov r8d, r12d
__sbr_cell_36_180_end:
__sbr_cell_36_181:
    call QWORD PTR [r15+48]
__sbr_cell_36_181_end:
sbr_qmf_synthesis.f8:
__sbr_cell_36_182:
    mov rax, QWORD PTR [rbp-184]
__sbr_cell_36_182_end:
__sbr_cell_36_183:
    lea rsi, [rax*4+0]
__sbr_cell_36_183_end:
__sbr_cell_36_184:
    add rsi, r13
__sbr_cell_36_184_end:
__sbr_cell_36_185:
    mov rdi, r14
__sbr_cell_36_185_end:
__sbr_cell_36_186:
    mov rdx, QWORD PTR [rbp-104]
__sbr_cell_36_186_end:
__sbr_cell_36_187:
    mov rcx, r14
__sbr_cell_36_187_end:
__sbr_cell_36_188:
    mov r8d, r12d
__sbr_cell_36_188_end:
__sbr_cell_36_189:
    call QWORD PTR [r15+48]
__sbr_cell_36_189_end:
sbr_qmf_synthesis.f9:
__sbr_cell_36_190:
    mov rax, QWORD PTR [rbp-176]
__sbr_cell_36_190_end:
__sbr_cell_36_191:
    lea rsi, [rax*4+0]
__sbr_cell_36_191_end:
__sbr_cell_36_192:
    add rsi, r13
__sbr_cell_36_192_end:
__sbr_cell_36_193:
    mov rdi, r14
__sbr_cell_36_193_end:
__sbr_cell_36_194:
    mov rdx, QWORD PTR [rbp-160]
__sbr_cell_36_194_end:
__sbr_cell_36_195:
    mov rcx, r14
__sbr_cell_36_195_end:
__sbr_cell_36_196:
    mov r8d, r12d
__sbr_cell_36_196_end:
__sbr_cell_36_197:
    call QWORD PTR [r15+48]
__sbr_cell_36_197_end:
sbr_qmf_synthesis.lend:
__sbr_cell_36_198:
    add rbx, 256
__sbr_cell_36_198_end:
__sbr_cell_36_199:
    add r14, QWORD PTR [rbp-152]
__sbr_cell_36_199_end:
__sbr_cell_36_200:
    mov rax, QWORD PTR [rbp-288]
__sbr_cell_36_200_end:
__sbr_cell_36_201:
    dec rax
__sbr_cell_36_201_end:
__sbr_cell_36_202:
    mov r13, QWORD PTR [rbp-264]
__sbr_cell_36_202_end:
__sbr_cell_36_203:
    je sbr_qmf_synthesis.La125
__sbr_cell_36_203_end:
sbr_qmf_synthesis.L9fd2:
__sbr_cell_36_204:
    mov QWORD PTR [rbp-288], rax
__sbr_cell_36_204_end:
__sbr_cell_36_205:
    mov rax, QWORD PTR [rbp+32]
__sbr_cell_36_205_end:
__sbr_cell_36_206:
    mov eax, DWORD PTR [rax+0]
__sbr_cell_36_206_end:
__sbr_cell_36_207:
    cmp eax, r13d
__sbr_cell_36_207_end:
__sbr_cell_36_208:
    jge sbr_qmf_synthesis.L9ff9
__sbr_cell_36_208_end:
sbr_qmf_synthesis.mc:
__sbr_cell_36_209:
    mov rdi, QWORD PTR [rbp-80]
__sbr_cell_36_209_end:
__sbr_cell_36_210:
    mov rsi, QWORD PTR [rbp+24]
__sbr_cell_36_210_end:
__sbr_cell_36_211:
    mov rdx, QWORD PTR [rbp-96]
__sbr_cell_36_211_end:
__sbr_cell_36_212:
    call memcpy
__sbr_cell_36_212_end:
sbr_qmf_synthesis.mc1:
__sbr_cell_36_213:
    mov rax, QWORD PTR [rbp-88]
__sbr_cell_36_213_end:
sbr_qmf_synthesis.L9ff9:
__sbr_cell_36_214:
    sub eax, r13d
__sbr_cell_36_214_end:
__sbr_cell_36_215:
    mov rcx, QWORD PTR [rbp+32]
__sbr_cell_36_215_end:
__sbr_cell_36_216:
    mov DWORD PTR [rcx+0], eax
__sbr_cell_36_216_end:
__sbr_cell_36_217:
    cdqe
__sbr_cell_36_217_end:
__sbr_cell_36_218:
    mov rcx, QWORD PTR [rbp+24]
__sbr_cell_36_218_end:
__sbr_cell_36_219:
    lea r13, [rcx+rax*4+0]
__sbr_cell_36_219_end:
__sbr_cell_36_220:
    cmp DWORD PTR [rbp+40], 0
__sbr_cell_36_220_end:
__sbr_cell_36_221:
    je sbr_qmf_synthesis.L9df0
__sbr_cell_36_221_end:
sbr_qmf_synthesis.ds:
__sbr_cell_36_222:
    vbroadcastss xmm1, DWORD PTR [rip+LCPI15_1]
__sbr_cell_36_222_end:
__sbr_cell_36_223:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+0]
__sbr_cell_36_223_end:
__sbr_cell_36_224:
    vmovups XMMWORD PTR [rbx+0], xmm0
__sbr_cell_36_224_end:
__sbr_cell_36_225:
    vpermilps xmm0, XMMWORD PTR [rbx+9840], 27
__sbr_cell_36_225_end:
__sbr_cell_36_226:
    vmovups XMMWORD PTR [rbx+128], xmm0
__sbr_cell_36_226_end:
__sbr_cell_36_227:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+16]
__sbr_cell_36_227_end:
__sbr_cell_36_228:
    vmovups XMMWORD PTR [rbx+16], xmm0
__sbr_cell_36_228_end:
__sbr_cell_36_229:
    vpermilps xmm0, XMMWORD PTR [rbx+9824], 27
__sbr_cell_36_229_end:
__sbr_cell_36_230:
    vmovups XMMWORD PTR [rbx+144], xmm0
__sbr_cell_36_230_end:
__sbr_cell_36_231:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+32]
__sbr_cell_36_231_end:
__sbr_cell_36_232:
    vmovups XMMWORD PTR [rbx+32], xmm0
__sbr_cell_36_232_end:
__sbr_cell_36_233:
    vpermilps xmm0, XMMWORD PTR [rbx+9808], 27
__sbr_cell_36_233_end:
__sbr_cell_36_234:
    vmovups XMMWORD PTR [rbx+160], xmm0
__sbr_cell_36_234_end:
__sbr_cell_36_235:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+48]
__sbr_cell_36_235_end:
__sbr_cell_36_236:
    vmovups XMMWORD PTR [rbx+48], xmm0
__sbr_cell_36_236_end:
__sbr_cell_36_237:
    vpermilps xmm0, XMMWORD PTR [rbx+9792], 27
__sbr_cell_36_237_end:
__sbr_cell_36_238:
    vmovups XMMWORD PTR [rbx+176], xmm0
__sbr_cell_36_238_end:
__sbr_cell_36_239:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+64]
__sbr_cell_36_239_end:
__sbr_cell_36_240:
    vmovups XMMWORD PTR [rbx+64], xmm0
__sbr_cell_36_240_end:
__sbr_cell_36_241:
    vpermilps xmm0, XMMWORD PTR [rbx+9776], 27
__sbr_cell_36_241_end:
__sbr_cell_36_242:
    vmovups XMMWORD PTR [rbx+192], xmm0
__sbr_cell_36_242_end:
__sbr_cell_36_243:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+80]
__sbr_cell_36_243_end:
__sbr_cell_36_244:
    vmovups XMMWORD PTR [rbx+80], xmm0
__sbr_cell_36_244_end:
__sbr_cell_36_245:
    vpermilps xmm0, XMMWORD PTR [rbx+9760], 27
__sbr_cell_36_245_end:
__sbr_cell_36_246:
    vmovups XMMWORD PTR [rbx+208], xmm0
__sbr_cell_36_246_end:
__sbr_cell_36_247:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+96]
__sbr_cell_36_247_end:
__sbr_cell_36_248:
    vmovups XMMWORD PTR [rbx+96], xmm0
__sbr_cell_36_248_end:
__sbr_cell_36_249:
    vpermilps xmm0, XMMWORD PTR [rbx+9744], 27
__sbr_cell_36_249_end:
__sbr_cell_36_250:
    vmovups XMMWORD PTR [rbx+224], xmm0
__sbr_cell_36_250_end:
__sbr_cell_36_251:
    vxorps xmm0, xmm1, XMMWORD PTR [rbx+112]
__sbr_cell_36_251_end:
__sbr_cell_36_252:
    vmovups XMMWORD PTR [rbx+112], xmm0
__sbr_cell_36_252_end:
__sbr_cell_36_253:
    vpermilps xmm0, XMMWORD PTR [rbx+9728], 27
__sbr_cell_36_253_end:
__sbr_cell_36_254:
    vmovups XMMWORD PTR [rbx+240], xmm0
__sbr_cell_36_254_end:
sbr_qmf_synthesis.ds1:
__sbr_cell_36_255:
    mov ecx, 4
__sbr_cell_36_255_end:
__sbr_cell_36_256:
    mov rdi, QWORD PTR [rbp-56]
__sbr_cell_36_256_end:
__sbr_cell_36_257:
    mov r12, QWORD PTR [rbp+16]
__sbr_cell_36_257_end:
__sbr_cell_36_258:
    mov rsi, r12
__sbr_cell_36_258_end:
__sbr_cell_36_259:
    mov rdx, rbx
__sbr_cell_36_259_end:
__sbr_cell_36_260:
    call QWORD PTR [rbp-64]
__sbr_cell_36_260_end:
sbr_qmf_synthesis.ds2:
__sbr_cell_36_261:
    mov rdi, r13
__sbr_cell_36_261_end:
__sbr_cell_36_262:
    mov rsi, r12
__sbr_cell_36_262_end:
__sbr_cell_36_263:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_36_263_end:
__sbr_cell_36_264:
    call QWORD PTR [rax+40]
__sbr_cell_36_264_end:
sbr_qmf_synthesis.ds3:
__sbr_cell_36_265:
    jmp sbr_qmf_synthesis.L9e42
__sbr_cell_36_265_end:
sbr_qmf_synthesis.La125:
__sbr_cell_36_266:
    add rsp, 248
__sbr_cell_36_266_end:
__sbr_cell_36_267:
    pop rbx
__sbr_cell_36_267_end:
__sbr_cell_36_268:
    pop r12
__sbr_cell_36_268_end:
__sbr_cell_36_269:
    pop r13
__sbr_cell_36_269_end:
__sbr_cell_36_270:
    pop r14
__sbr_cell_36_270_end:
__sbr_cell_36_271:
    pop r15
__sbr_cell_36_271_end:
__sbr_cell_36_272:
    pop rbp
__sbr_cell_36_272_end:
sbr_qmf_synthesis.done:
__sbr_cell_36_273:
    ret
__sbr_cell_36_273_end:
__sbr_cell_36_274:
    int3
__sbr_cell_36_274_end:
__sbr_cell_36_275:
    int3
__sbr_cell_36_275_end:
__sbr_cell_36_276:
    int3
__sbr_cell_36_276_end:
__sbr_cell_36_277:
    int3
__sbr_cell_36_277_end:
__sbr_cell_36_278:
    int3
__sbr_cell_36_278_end:
__sbr_cell_36_279:
    int3
__sbr_cell_36_279_end:
__sbr_cell_36_280:
    int3
__sbr_cell_36_280_end:
__sbr_cell_36_281:
    int3
__sbr_cell_36_281_end:
__sbr_cell_36_282:
    int3
__sbr_cell_36_282_end:
.size sbr_qmf_synthesis, .-sbr_qmf_synthesis
.section .text.sbr_reset,"ax",@progbits
.globl sbr_reset
.type sbr_reset,@function
sbr_reset:
__sbr_cell_37_0:
    push rbp
__sbr_cell_37_0_end:
__sbr_cell_37_1:
    mov rbp, rsp
__sbr_cell_37_1_end:
__sbr_cell_37_2:
    push r15
__sbr_cell_37_2_end:
sbr_reset.L1086:
__sbr_cell_37_3:
    push r14
__sbr_cell_37_3_end:
__sbr_cell_37_4:
    push r13
__sbr_cell_37_4_end:
sbr_reset.L108a:
__sbr_cell_37_5:
    push r12
__sbr_cell_37_5_end:
__sbr_cell_37_6:
    push rbx
__sbr_cell_37_6_end:
__sbr_cell_37_7:
    sub rsp, 1352
__sbr_cell_37_7_end:
__sbr_cell_37_8:
    mov r12, rsi
__sbr_cell_37_8_end:
__sbr_cell_37_9:
    mov r15, rdi
__sbr_cell_37_9_end:
__sbr_cell_37_10:
    mov ecx, DWORD PTR [rsi+0]
__sbr_cell_37_10_end:
__sbr_cell_37_11:
    cmp ecx, 63999
__sbr_cell_37_11_end:
__sbr_cell_37_12:
    jg sbr_reset.L10d9
__sbr_cell_37_12_end:
__sbr_cell_37_13:
    cmp ecx, 31999
__sbr_cell_37_13_end:
__sbr_cell_37_14:
    jg sbr_reset.L10fe
__sbr_cell_37_14_end:
__sbr_cell_37_15:
    cmp ecx, 16000
__sbr_cell_37_15_end:
__sbr_cell_37_16:
    je sbr_reset.L17fc
__sbr_cell_37_16_end:
sbr_reset.L10b8:
__sbr_cell_37_17:
    cmp ecx, 22050
__sbr_cell_37_17_end:
__sbr_cell_37_18:
    je sbr_reset.L1814
__sbr_cell_37_18_end:
__sbr_cell_37_19:
    cmp ecx, 24000
__sbr_cell_37_19_end:
__sbr_cell_37_20:
    jne sbr_reset.L1820
__sbr_cell_37_20_end:
__sbr_cell_37_21:
    lea rdi, [rip+sbr_offset_2]
__sbr_cell_37_21_end:
__sbr_cell_37_22:
    jmp sbr_reset.L114a
__sbr_cell_37_22_end:
sbr_reset.L10d9:
__sbr_cell_37_23:
    cmp ecx, 127999
__sbr_cell_37_23_end:
__sbr_cell_37_24:
    jg sbr_reset.L1127
__sbr_cell_37_24_end:
__sbr_cell_37_25:
    cmp ecx, 64000
__sbr_cell_37_25_end:
__sbr_cell_37_26:
    je sbr_reset.L111e
__sbr_cell_37_26_end:
__sbr_cell_37_27:
    cmp ecx, 88200
__sbr_cell_37_27_end:
__sbr_cell_37_28:
    je sbr_reset.L1143
__sbr_cell_37_28_end:
__sbr_cell_37_29:
    cmp ecx, 96000
__sbr_cell_37_29_end:
__sbr_cell_37_30:
    je sbr_reset.L1143
__sbr_cell_37_30_end:
__sbr_cell_37_31:
    jmp sbr_reset.L1820
__sbr_cell_37_31_end:
sbr_reset.L10fe:
__sbr_cell_37_32:
    cmp ecx, 32000
__sbr_cell_37_32_end:
__sbr_cell_37_33:
    je sbr_reset.L1808
__sbr_cell_37_33_end:
__sbr_cell_37_34:
    cmp ecx, 44100
__sbr_cell_37_34_end:
__sbr_cell_37_35:
    je sbr_reset.L111e
__sbr_cell_37_35_end:
__sbr_cell_37_36:
    cmp ecx, 48000
__sbr_cell_37_36_end:
__sbr_cell_37_37:
    jne sbr_reset.L1820
__sbr_cell_37_37_end:
sbr_reset.L111e:
__sbr_cell_37_38:
    lea rdi, [rip+sbr_offset_4]
__sbr_cell_37_38_end:
__sbr_cell_37_39:
    jmp sbr_reset.L114a
__sbr_cell_37_39_end:
sbr_reset.L1127:
__sbr_cell_37_40:
    cmp ecx, 128000
__sbr_cell_37_40_end:
__sbr_cell_37_41:
    je sbr_reset.L1143
__sbr_cell_37_41_end:
__sbr_cell_37_42:
    cmp ecx, 176400
__sbr_cell_37_42_end:
__sbr_cell_37_43:
    je sbr_reset.L1143
__sbr_cell_37_43_end:
__sbr_cell_37_44:
    cmp ecx, 192000
__sbr_cell_37_44_end:
__sbr_cell_37_45:
    jne sbr_reset.L1820
__sbr_cell_37_45_end:
sbr_reset.L1143:
__sbr_cell_37_46:
    lea rdi, [rip+sbr_offset_5]
__sbr_cell_37_46_end:
sbr_reset.L114a:
__sbr_cell_37_47:
    cmp ecx, 64000
__sbr_cell_37_47_end:
__sbr_cell_37_48:
    mov eax, 4000
__sbr_cell_37_48_end:
__sbr_cell_37_49:
    mov edx, 5000
__sbr_cell_37_49_end:
__sbr_cell_37_50:
    cmovb edx, eax
__sbr_cell_37_50_end:
__sbr_cell_37_51:
    cmp ecx, 32000
__sbr_cell_37_51_end:
__sbr_cell_37_52:
    mov esi, 3000
__sbr_cell_37_52_end:
__sbr_cell_37_53:
    cmovae esi, edx
__sbr_cell_37_53_end:
__sbr_cell_37_54:
    mov eax, esi
__sbr_cell_37_54_end:
__sbr_cell_37_55:
    shl eax, 7
__sbr_cell_37_55_end:
__sbr_cell_37_56:
    mov r8d, ecx
__sbr_cell_37_56_end:
__sbr_cell_37_57:
    shr r8d, 1
__sbr_cell_37_57_end:
__sbr_cell_37_58:
    add eax, r8d
__sbr_cell_37_58_end:
sbr_reset.L1179:
__sbr_cell_37_59:
    xor edx, edx
__sbr_cell_37_59_end:
__sbr_cell_37_60:
    div ecx
__sbr_cell_37_60_end:
sbr_reset.L117d:
__sbr_cell_37_61:
    movzx edx, BYTE PTR [r12+28]
__sbr_cell_37_61_end:
__sbr_cell_37_62:
    movsx edx, BYTE PTR [rdi+rdx*1+0]
__sbr_cell_37_62_end:
__sbr_cell_37_63:
    add edx, eax
__sbr_cell_37_63_end:
__sbr_cell_37_64:
    mov DWORD PTR [r12+64], edx
__sbr_cell_37_64_end:
sbr_reset.L118e:
__sbr_cell_37_65:
    movzx eax, BYTE PTR [r12+29]
__sbr_cell_37_65_end:
__sbr_cell_37_66:
    cmp eax, 13
__sbr_cell_37_66_end:
__sbr_cell_37_67:
    ja sbr_reset.L150a
__sbr_cell_37_67_end:
__sbr_cell_37_68:
    mov QWORD PTR [rbp-64], r15
__sbr_cell_37_68_end:
__sbr_cell_37_69:
    shl esi, 8
__sbr_cell_37_69_end:
__sbr_cell_37_70:
    add esi, r8d
__sbr_cell_37_70_end:
sbr_reset.L11a7:
__sbr_cell_37_71:
    mov eax, esi
__sbr_cell_37_71_end:
__sbr_cell_37_72:
    xor edx, edx
__sbr_cell_37_72_end:
__sbr_cell_37_73:
    div ecx
__sbr_cell_37_73_end:
sbr_reset.L11ad:
__sbr_cell_37_74:
    mov r15d, eax
__sbr_cell_37_74_end:
__sbr_cell_37_75:
    mov QWORD PTR [rbp-48], r12
__sbr_cell_37_75_end:
__sbr_cell_37_76:
    mov DWORD PTR [r12+72], eax
__sbr_cell_37_76_end:
__sbr_cell_37_77:
    vcvtsi2ss xmm1, xmm15, eax
__sbr_cell_37_77_end:
sbr_reset.L11bd:
__sbr_cell_37_78:
    vmovss DWORD PTR [rbp-56], xmm1
__sbr_cell_37_78_end:
__sbr_cell_37_79:
    vmovss xmm0, DWORD PTR [rip+LCPI5_0]
__sbr_cell_37_79_end:
__sbr_cell_37_80:
    vdivss xmm0, xmm0, xmm1
__sbr_cell_37_80_end:
__sbr_cell_37_81:
    vmovss xmm1, DWORD PTR [rip+LCPI5_1]
__sbr_cell_37_81_end:
__sbr_cell_37_82:
    call powf
__sbr_cell_37_82_end:
sbr_reset.L11db:
__sbr_cell_37_83:
    vmulss xmm1, xmm0, DWORD PTR [rbp-56]
__sbr_cell_37_83_end:
__sbr_cell_37_84:
    vmulss xmm2, xmm0, xmm1
__sbr_cell_37_84_end:
__sbr_cell_37_85:
    vcvtss2si rax, xmm2
__sbr_cell_37_85_end:
__sbr_cell_37_86:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_86_end:
__sbr_cell_37_87:
    vcvtss2si rcx, xmm2
__sbr_cell_37_87_end:
__sbr_cell_37_88:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_88_end:
__sbr_cell_37_89:
    vcvtss2si rdx, xmm2
__sbr_cell_37_89_end:
__sbr_cell_37_90:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_90_end:
__sbr_cell_37_91:
    vcvtss2si rsi, xmm2
__sbr_cell_37_91_end:
__sbr_cell_37_92:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_92_end:
__sbr_cell_37_93:
    vcvtss2si rdi, xmm2
__sbr_cell_37_93_end:
__sbr_cell_37_94:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_94_end:
sbr_reset.L1211:
__sbr_cell_37_95:
    vcvtss2si r8, xmm2
__sbr_cell_37_95_end:
__sbr_cell_37_96:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_96_end:
__sbr_cell_37_97:
    vcvtss2si r9, xmm2
__sbr_cell_37_97_end:
__sbr_cell_37_98:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_98_end:
__sbr_cell_37_99:
    vcvtss2si r11, xmm2
__sbr_cell_37_99_end:
__sbr_cell_37_100:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_100_end:
__sbr_cell_37_101:
    vcvtss2si r13, xmm2
__sbr_cell_37_101_end:
__sbr_cell_37_102:
    vmulss xmm2, xmm0, xmm2
__sbr_cell_37_102_end:
__sbr_cell_37_103:
    vcvtss2si r12, xmm2
__sbr_cell_37_103_end:
__sbr_cell_37_104:
    vmulss xmm0, xmm0, xmm2
__sbr_cell_37_104_end:
__sbr_cell_37_105:
    vcvtss2si r14, xmm0
__sbr_cell_37_105_end:
__sbr_cell_37_106:
    mov r10d, 64
__sbr_cell_37_106_end:
sbr_reset.L1249:
__sbr_cell_37_107:
    sub r10d, r14d
__sbr_cell_37_107_end:
__sbr_cell_37_108:
    sub r14d, r12d
__sbr_cell_37_108_end:
__sbr_cell_37_109:
    sub r12d, r13d
__sbr_cell_37_109_end:
__sbr_cell_37_110:
    sub r13d, r11d
__sbr_cell_37_110_end:
__sbr_cell_37_111:
    sub r11d, r9d
__sbr_cell_37_111_end:
__sbr_cell_37_112:
    sub r9d, r8d
__sbr_cell_37_112_end:
__sbr_cell_37_113:
    sub r8d, edi
__sbr_cell_37_113_end:
__sbr_cell_37_114:
    sub edi, esi
__sbr_cell_37_114_end:
__sbr_cell_37_115:
    sub esi, edx
__sbr_cell_37_115_end:
__sbr_cell_37_116:
    sub edx, ecx
__sbr_cell_37_116_end:
__sbr_cell_37_117:
    sub ecx, eax
__sbr_cell_37_117_end:
__sbr_cell_37_118:
    vcvtss2si rbx, xmm1
__sbr_cell_37_118_end:
sbr_reset.L126b:
__sbr_cell_37_119:
    sub eax, ebx
__sbr_cell_37_119_end:
__sbr_cell_37_120:
    sub ebx, r15d
__sbr_cell_37_120_end:
__sbr_cell_37_121:
    mov WORD PTR [rbp-112], bx
__sbr_cell_37_121_end:
__sbr_cell_37_122:
    mov WORD PTR [rbp-110], ax
__sbr_cell_37_122_end:
sbr_reset.L1278:
__sbr_cell_37_123:
    mov WORD PTR [rbp-108], cx
__sbr_cell_37_123_end:
__sbr_cell_37_124:
    mov WORD PTR [rbp-106], dx
__sbr_cell_37_124_end:
sbr_reset.L1280:
__sbr_cell_37_125:
    mov WORD PTR [rbp-104], si
__sbr_cell_37_125_end:
__sbr_cell_37_126:
    mov WORD PTR [rbp-102], di
__sbr_cell_37_126_end:
sbr_reset.L1288:
__sbr_cell_37_127:
    mov WORD PTR [rbp-100], r8w
__sbr_cell_37_127_end:
__sbr_cell_37_128:
    mov WORD PTR [rbp-98], r9w
__sbr_cell_37_128_end:
sbr_reset.L1292:
__sbr_cell_37_129:
    mov WORD PTR [rbp-96], r11w
__sbr_cell_37_129_end:
__sbr_cell_37_130:
    mov WORD PTR [rbp-94], r13w
__sbr_cell_37_130_end:
sbr_reset.L129c:
__sbr_cell_37_131:
    mov WORD PTR [rbp-92], r12w
__sbr_cell_37_131_end:
__sbr_cell_37_132:
    mov WORD PTR [rbp-90], r14w
__sbr_cell_37_132_end:
__sbr_cell_37_133:
    lea rax, [rbp-88]
__sbr_cell_37_133_end:
sbr_reset.L12aa:
__sbr_cell_37_134:
    mov WORD PTR [rbp-88], r10w
__sbr_cell_37_134_end:
__sbr_cell_37_135:
    lea rcx, [rbp-112]
__sbr_cell_37_135_end:
__sbr_cell_37_136:
    mov QWORD PTR [rbp-1392], rcx
__sbr_cell_37_136_end:
sbr_reset.L12ba:
__sbr_cell_37_137:
    mov QWORD PTR [rbp-1384], rax
__sbr_cell_37_137_end:
__sbr_cell_37_138:
    mov eax, 1
__sbr_cell_37_138_end:
__sbr_cell_37_139:
    jmp sbr_reset.L12d8
__sbr_cell_37_139_end:
__sbr_cell_37_140:
    .nops 1
__sbr_cell_37_140_end:
sbr_reset.L12d0:
__sbr_cell_37_141:
    test eax, eax
__sbr_cell_37_141_end:
__sbr_cell_37_142:
    je sbr_reset.L1523
__sbr_cell_37_142_end:
sbr_reset.L12d8:
__sbr_cell_37_143:
    cmp eax, 65
__sbr_cell_37_143_end:
__sbr_cell_37_144:
    jae sbr_reset.L3257
__sbr_cell_37_144_end:
__sbr_cell_37_145:
    dec eax
__sbr_cell_37_145_end:
__sbr_cell_37_146:
    mov rcx, rax
__sbr_cell_37_146_end:
__sbr_cell_37_147:
    shl rcx, 4
__sbr_cell_37_147_end:
__sbr_cell_37_148:
    mov rdx, QWORD PTR [rbp+rcx*1-1392]
__sbr_cell_37_148_end:
__sbr_cell_37_149:
    mov rcx, QWORD PTR [rbp+rcx*1-1384]
__sbr_cell_37_149_end:
__sbr_cell_37_150:
    .nops 1
__sbr_cell_37_150_end:
sbr_reset.L1300:
__sbr_cell_37_151:
    cmp rdx, rcx
__sbr_cell_37_151_end:
__sbr_cell_37_152:
    jae sbr_reset.L12d0
__sbr_cell_37_152_end:
__sbr_cell_37_153:
    lea rdi, [rcx-2]
__sbr_cell_37_153_end:
__sbr_cell_37_154:
    cmp rdx, rdi
__sbr_cell_37_154_end:
__sbr_cell_37_155:
    jae sbr_reset.L14f0
__sbr_cell_37_155_end:
__sbr_cell_37_156:
    mov r8, rcx
__sbr_cell_37_156_end:
__sbr_cell_37_157:
    sub r8, rdx
__sbr_cell_37_157_end:
__sbr_cell_37_158:
    sar r8, 2
__sbr_cell_37_158_end:
__sbr_cell_37_159:
    lea rsi, [rdx+r8*2+0]
__sbr_cell_37_159_end:
__sbr_cell_37_160:
    movzx r9d, WORD PTR [rdx+0]
__sbr_cell_37_160_end:
__sbr_cell_37_161:
    movzx r11d, WORD PTR [rcx+0]
__sbr_cell_37_161_end:
__sbr_cell_37_162:
    movzx r8d, WORD PTR [rdx+r8*2+0]
__sbr_cell_37_162_end:
sbr_reset.L132d:
__sbr_cell_37_163:
    cmp r9w, r11w
__sbr_cell_37_163_end:
__sbr_cell_37_164:
    jle sbr_reset.L1350
__sbr_cell_37_164_end:
__sbr_cell_37_165:
    cmp r11w, r8w
__sbr_cell_37_165_end:
__sbr_cell_37_166:
    jg sbr_reset.L135c
__sbr_cell_37_166_end:
__sbr_cell_37_167:
    mov WORD PTR [rcx+0], r9w
__sbr_cell_37_167_end:
__sbr_cell_37_168:
    mov r8d, r11d
__sbr_cell_37_168_end:
__sbr_cell_37_169:
    jmp sbr_reset.L1360
__sbr_cell_37_169_end:
__sbr_cell_37_170:
    .nops 1
__sbr_cell_37_170_end:
sbr_reset.L1350:
__sbr_cell_37_171:
    mov r10d, 1
__sbr_cell_37_171_end:
__sbr_cell_37_172:
    cmp r9w, r8w
__sbr_cell_37_172_end:
__sbr_cell_37_173:
    jle sbr_reset.L136f
__sbr_cell_37_173_end:
sbr_reset.L135c:
__sbr_cell_37_174:
    mov WORD PTR [rsi+0], r9w
__sbr_cell_37_174_end:
sbr_reset.L1360:
__sbr_cell_37_175:
    mov WORD PTR [rdx+0], r8w
__sbr_cell_37_175_end:
__sbr_cell_37_176:
    movzx r8d, WORD PTR [rsi+0]
__sbr_cell_37_176_end:
__sbr_cell_37_177:
    movzx r11d, WORD PTR [rcx+0]
__sbr_cell_37_177_end:
__sbr_cell_37_178:
    xor r10d, r10d
__sbr_cell_37_178_end:
sbr_reset.L136f:
__sbr_cell_37_179:
    cmp r8w, r11w
__sbr_cell_37_179_end:
__sbr_cell_37_180:
    jle sbr_reset.L1390
__sbr_cell_37_180_end:
__sbr_cell_37_181:
    mov WORD PTR [rcx+0], r8w
__sbr_cell_37_181_end:
__sbr_cell_37_182:
    mov WORD PTR [rsi+0], r11w
__sbr_cell_37_182_end:
__sbr_cell_37_183:
    xor r10d, r10d
__sbr_cell_37_183_end:
__sbr_cell_37_184:
    lea r8, [rcx-4]
__sbr_cell_37_184_end:
__sbr_cell_37_185:
    cmp rdx, r8
__sbr_cell_37_185_end:
__sbr_cell_37_186:
    jne sbr_reset.L13a0
__sbr_cell_37_186_end:
__sbr_cell_37_187:
    jmp sbr_reset.L12d0
__sbr_cell_37_187_end:
__sbr_cell_37_188:
    .nops 1
__sbr_cell_37_188_end:
sbr_reset.L1390:
__sbr_cell_37_189:
    mov r11d, r8d
__sbr_cell_37_189_end:
__sbr_cell_37_190:
    lea r8, [rcx-4]
__sbr_cell_37_190_end:
__sbr_cell_37_191:
    cmp rdx, r8
__sbr_cell_37_191_end:
__sbr_cell_37_192:
    je sbr_reset.L12d0
__sbr_cell_37_192_end:
sbr_reset.L13a0:
__sbr_cell_37_193:
    lea r9, [rdx+2]
__sbr_cell_37_193_end:
__sbr_cell_37_194:
    movzx ebx, WORD PTR [rdi+0]
__sbr_cell_37_194_end:
__sbr_cell_37_195:
    mov WORD PTR [rsi+0], bx
__sbr_cell_37_195_end:
__sbr_cell_37_196:
    mov WORD PTR [rdi+0], r11w
__sbr_cell_37_196_end:
__sbr_cell_37_197:
    cmp r9, r8
__sbr_cell_37_197_end:
__sbr_cell_37_198:
    jbe sbr_reset.L13d9
__sbr_cell_37_198_end:
__sbr_cell_37_199:
    jmp sbr_reset.L1424
__sbr_cell_37_199_end:
__sbr_cell_37_200:
    .nops 1
__sbr_cell_37_200_end:
sbr_reset.L13c0:
__sbr_cell_37_201:
    movzx r11d, WORD PTR [r9+0]
__sbr_cell_37_201_end:
__sbr_cell_37_202:
    mov WORD PTR [r8+0], r11w
__sbr_cell_37_202_end:
__sbr_cell_37_203:
    mov WORD PTR [r9+0], r14w
__sbr_cell_37_203_end:
__sbr_cell_37_204:
    add r9, 2
__sbr_cell_37_204_end:
__sbr_cell_37_205:
    add r8, -2
__sbr_cell_37_205_end:
sbr_reset.L13d4:
__sbr_cell_37_206:
    cmp r9, r8
__sbr_cell_37_206_end:
__sbr_cell_37_207:
    ja sbr_reset.L1420
__sbr_cell_37_207_end:
sbr_reset.L13d9:
__sbr_cell_37_208:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_208_end:
__sbr_cell_37_209:
    .nops 1
__sbr_cell_37_209_end:
sbr_reset.L13e0:
__sbr_cell_37_210:
    cmp WORD PTR [r9+0], r11w
__sbr_cell_37_210_end:
__sbr_cell_37_211:
    jge sbr_reset.L1404
__sbr_cell_37_211_end:
__sbr_cell_37_212:
    add r9, 2
__sbr_cell_37_212_end:
__sbr_cell_37_213:
    cmp r9, r8
__sbr_cell_37_213_end:
__sbr_cell_37_214:
    jbe sbr_reset.L13e0
__sbr_cell_37_214_end:
__sbr_cell_37_215:
    jmp sbr_reset.L1404
__sbr_cell_37_215_end:
__sbr_cell_37_216:
    .nops 1
__sbr_cell_37_216_end:
sbr_reset.L1400:
__sbr_cell_37_217:
    add r8, -2
__sbr_cell_37_217_end:
sbr_reset.L1404:
__sbr_cell_37_218:
    cmp r9, r8
__sbr_cell_37_218_end:
__sbr_cell_37_219:
    ja sbr_reset.L13d4
__sbr_cell_37_219_end:
__sbr_cell_37_220:
    movzx r14d, WORD PTR [r8+0]
__sbr_cell_37_220_end:
__sbr_cell_37_221:
    cmp r14w, r11w
__sbr_cell_37_221_end:
__sbr_cell_37_222:
    jg sbr_reset.L1400
__sbr_cell_37_222_end:
__sbr_cell_37_223:
    jmp sbr_reset.L13c0
__sbr_cell_37_223_end:
__sbr_cell_37_224:
    .nops 1
__sbr_cell_37_224_end:
sbr_reset.L1420:
__sbr_cell_37_225:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_225_end:
sbr_reset.L1424:
__sbr_cell_37_226:
    movzx ebx, WORD PTR [r9+0]
__sbr_cell_37_226_end:
__sbr_cell_37_227:
    mov WORD PTR [r9+0], r11w
__sbr_cell_37_227_end:
__sbr_cell_37_228:
    mov WORD PTR [rdi+0], bx
__sbr_cell_37_228_end:
__sbr_cell_37_229:
    test r10d, r10d
__sbr_cell_37_229_end:
__sbr_cell_37_230:
    je sbr_reset.L1470
__sbr_cell_37_230_end:
__sbr_cell_37_231:
    cmp rsi, r9
__sbr_cell_37_231_end:
__sbr_cell_37_232:
    je sbr_reset.L1442
__sbr_cell_37_232_end:
__sbr_cell_37_233:
    lea rdi, [r9-2]
__sbr_cell_37_233_end:
__sbr_cell_37_234:
    cmp rsi, rdi
__sbr_cell_37_234_end:
__sbr_cell_37_235:
    jne sbr_reset.L1470
__sbr_cell_37_235_end:
sbr_reset.L1442:
__sbr_cell_37_236:
    mov rdi, rdx
__sbr_cell_37_236_end:
__sbr_cell_37_237:
    .nops 1
__sbr_cell_37_237_end:
sbr_reset.L1450:
__sbr_cell_37_238:
    mov rsi, rdi
__sbr_cell_37_238_end:
__sbr_cell_37_239:
    cmp rdi, rcx
__sbr_cell_37_239_end:
__sbr_cell_37_240:
    jae sbr_reset.L1467
__sbr_cell_37_240_end:
__sbr_cell_37_241:
    lea rdi, [rsi+2]
__sbr_cell_37_241_end:
__sbr_cell_37_242:
    movzx r10d, WORD PTR [rsi+0]
__sbr_cell_37_242_end:
__sbr_cell_37_243:
    cmp r10w, WORD PTR [rsi+2]
__sbr_cell_37_243_end:
__sbr_cell_37_244:
    jle sbr_reset.L1450
__sbr_cell_37_244_end:
sbr_reset.L1467:
__sbr_cell_37_245:
    cmp rsi, rcx
__sbr_cell_37_245_end:
__sbr_cell_37_246:
    je sbr_reset.L12d0
__sbr_cell_37_246_end:
sbr_reset.L1470:
__sbr_cell_37_247:
    mov rsi, rcx
__sbr_cell_37_247_end:
__sbr_cell_37_248:
    sub rsi, r9
__sbr_cell_37_248_end:
__sbr_cell_37_249:
    mov rdi, r9
__sbr_cell_37_249_end:
__sbr_cell_37_250:
    sub rdi, rdx
__sbr_cell_37_250_end:
__sbr_cell_37_251:
    cmp rsi, rdi
__sbr_cell_37_251_end:
__sbr_cell_37_252:
    jge sbr_reset.L14c0
__sbr_cell_37_252_end:
__sbr_cell_37_253:
    cmp rax, 64
__sbr_cell_37_253_end:
__sbr_cell_37_254:
    jae sbr_reset.L324d
__sbr_cell_37_254_end:
__sbr_cell_37_255:
    mov rsi, rax
__sbr_cell_37_255_end:
__sbr_cell_37_256:
    shl rsi, 4
__sbr_cell_37_256_end:
__sbr_cell_37_257:
    mov QWORD PTR [rbp+rsi*1-1392], rdx
__sbr_cell_37_257_end:
__sbr_cell_37_258:
    mov QWORD PTR [rbp+rsi*1-1384], r8
__sbr_cell_37_258_end:
sbr_reset.L14a2:
__sbr_cell_37_259:
    add r9, 2
__sbr_cell_37_259_end:
__sbr_cell_37_260:
    mov rdx, r9
__sbr_cell_37_260_end:
__sbr_cell_37_261:
    inc rax
__sbr_cell_37_261_end:
__sbr_cell_37_262:
    jmp sbr_reset.L1300
__sbr_cell_37_262_end:
__sbr_cell_37_263:
    .nops 1
__sbr_cell_37_263_end:
sbr_reset.L14c0:
__sbr_cell_37_264:
    cmp rax, 64
__sbr_cell_37_264_end:
__sbr_cell_37_265:
    jae sbr_reset.L3252
__sbr_cell_37_265_end:
__sbr_cell_37_266:
    add r9, 2
__sbr_cell_37_266_end:
__sbr_cell_37_267:
    mov rsi, rax
__sbr_cell_37_267_end:
__sbr_cell_37_268:
    shl rsi, 4
__sbr_cell_37_268_end:
__sbr_cell_37_269:
    mov QWORD PTR [rbp+rsi*1-1392], r9
__sbr_cell_37_269_end:
__sbr_cell_37_270:
    mov QWORD PTR [rbp+rsi*1-1384], rcx
__sbr_cell_37_270_end:
__sbr_cell_37_271:
    mov rcx, r8
__sbr_cell_37_271_end:
__sbr_cell_37_272:
    inc rax
__sbr_cell_37_272_end:
__sbr_cell_37_273:
    jmp sbr_reset.L1300
__sbr_cell_37_273_end:
sbr_reset.L14f0:
__sbr_cell_37_274:
    movzx esi, WORD PTR [rdx+0]
__sbr_cell_37_274_end:
__sbr_cell_37_275:
    movzx edi, WORD PTR [rcx+0]
__sbr_cell_37_275_end:
__sbr_cell_37_276:
    cmp si, di
__sbr_cell_37_276_end:
__sbr_cell_37_277:
    jle sbr_reset.L12d0
__sbr_cell_37_277_end:
__sbr_cell_37_278:
    mov WORD PTR [rcx+0], si
__sbr_cell_37_278_end:
__sbr_cell_37_279:
    mov WORD PTR [rdx+0], di
__sbr_cell_37_279_end:
__sbr_cell_37_280:
    jmp sbr_reset.L12d0
__sbr_cell_37_280_end:
sbr_reset.L150a:
__sbr_cell_37_281:
    cmp eax, 15
__sbr_cell_37_281_end:
__sbr_cell_37_282:
    je sbr_reset.L161f
__sbr_cell_37_282_end:
__sbr_cell_37_283:
    cmp eax, 14
__sbr_cell_37_283_end:
__sbr_cell_37_284:
    jne sbr_reset.L1762
__sbr_cell_37_284_end:
__sbr_cell_37_285:
    add edx, edx
__sbr_cell_37_285_end:
__sbr_cell_37_286:
    jmp sbr_reset.L1622
__sbr_cell_37_286_end:
sbr_reset.L1523:
__sbr_cell_37_287:
    mov r12, QWORD PTR [rbp-48]
__sbr_cell_37_287_end:
__sbr_cell_37_288:
    movzx eax, BYTE PTR [r12+29]
__sbr_cell_37_288_end:
__sbr_cell_37_289:
    test al, al
__sbr_cell_37_289_end:
__sbr_cell_37_290:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_290_end:
__sbr_cell_37_291:
    je sbr_reset.L1618
__sbr_cell_37_291_end:
__sbr_cell_37_292:
    movsx edx, WORD PTR [rbp-112]
__sbr_cell_37_292_end:
__sbr_cell_37_293:
    add edx, DWORD PTR [r12+72]
__sbr_cell_37_293_end:
__sbr_cell_37_294:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_294_end:
__sbr_cell_37_295:
    cmp al, 1
__sbr_cell_37_295_end:
__sbr_cell_37_296:
    je sbr_reset.L1622
__sbr_cell_37_296_end:
__sbr_cell_37_297:
    movsx ecx, WORD PTR [rbp-110]
__sbr_cell_37_297_end:
__sbr_cell_37_298:
    add edx, ecx
__sbr_cell_37_298_end:
sbr_reset.L1555:
__sbr_cell_37_299:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_299_end:
__sbr_cell_37_300:
    cmp al, 3
__sbr_cell_37_300_end:
__sbr_cell_37_301:
    jb sbr_reset.L1622
__sbr_cell_37_301_end:
__sbr_cell_37_302:
    movsx ecx, WORD PTR [rbp-108]
__sbr_cell_37_302_end:
__sbr_cell_37_303:
    add edx, ecx
__sbr_cell_37_303_end:
__sbr_cell_37_304:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_304_end:
__sbr_cell_37_305:
    cmp al, 3
__sbr_cell_37_305_end:
__sbr_cell_37_306:
    je sbr_reset.L1622
__sbr_cell_37_306_end:
__sbr_cell_37_307:
    movsx ecx, WORD PTR [rbp-106]
__sbr_cell_37_307_end:
__sbr_cell_37_308:
    add edx, ecx
__sbr_cell_37_308_end:
sbr_reset.L157b:
__sbr_cell_37_309:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_309_end:
__sbr_cell_37_310:
    cmp al, 5
__sbr_cell_37_310_end:
__sbr_cell_37_311:
    jb sbr_reset.L1622
__sbr_cell_37_311_end:
__sbr_cell_37_312:
    movsx ecx, WORD PTR [rbp-104]
__sbr_cell_37_312_end:
__sbr_cell_37_313:
    add edx, ecx
__sbr_cell_37_313_end:
__sbr_cell_37_314:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_314_end:
__sbr_cell_37_315:
    cmp al, 5
__sbr_cell_37_315_end:
__sbr_cell_37_316:
    je sbr_reset.L1622
__sbr_cell_37_316_end:
__sbr_cell_37_317:
    movsx ecx, WORD PTR [rbp-102]
__sbr_cell_37_317_end:
__sbr_cell_37_318:
    add edx, ecx
__sbr_cell_37_318_end:
sbr_reset.L15a1:
__sbr_cell_37_319:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_319_end:
__sbr_cell_37_320:
    cmp al, 7
__sbr_cell_37_320_end:
__sbr_cell_37_321:
    jb sbr_reset.L1622
__sbr_cell_37_321_end:
__sbr_cell_37_322:
    movsx ecx, WORD PTR [rbp-100]
__sbr_cell_37_322_end:
__sbr_cell_37_323:
    add edx, ecx
__sbr_cell_37_323_end:
__sbr_cell_37_324:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_324_end:
__sbr_cell_37_325:
    cmp al, 7
__sbr_cell_37_325_end:
__sbr_cell_37_326:
    je sbr_reset.L1622
__sbr_cell_37_326_end:
__sbr_cell_37_327:
    movsx ecx, WORD PTR [rbp-98]
__sbr_cell_37_327_end:
__sbr_cell_37_328:
    add edx, ecx
__sbr_cell_37_328_end:
sbr_reset.L15bf:
__sbr_cell_37_329:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_329_end:
__sbr_cell_37_330:
    cmp al, 9
__sbr_cell_37_330_end:
__sbr_cell_37_331:
    jb sbr_reset.L1622
__sbr_cell_37_331_end:
__sbr_cell_37_332:
    movsx ecx, WORD PTR [rbp-96]
__sbr_cell_37_332_end:
__sbr_cell_37_333:
    add edx, ecx
__sbr_cell_37_333_end:
__sbr_cell_37_334:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_334_end:
__sbr_cell_37_335:
    cmp al, 9
__sbr_cell_37_335_end:
__sbr_cell_37_336:
    je sbr_reset.L1622
__sbr_cell_37_336_end:
__sbr_cell_37_337:
    movsx ecx, WORD PTR [rbp-94]
__sbr_cell_37_337_end:
__sbr_cell_37_338:
    add edx, ecx
__sbr_cell_37_338_end:
sbr_reset.L15dd:
__sbr_cell_37_339:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_339_end:
__sbr_cell_37_340:
    cmp al, 11
__sbr_cell_37_340_end:
__sbr_cell_37_341:
    jb sbr_reset.L1622
__sbr_cell_37_341_end:
__sbr_cell_37_342:
    movsx ecx, WORD PTR [rbp-92]
__sbr_cell_37_342_end:
__sbr_cell_37_343:
    add edx, ecx
__sbr_cell_37_343_end:
__sbr_cell_37_344:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_344_end:
__sbr_cell_37_345:
    cmp al, 11
__sbr_cell_37_345_end:
__sbr_cell_37_346:
    je sbr_reset.L1622
__sbr_cell_37_346_end:
__sbr_cell_37_347:
    movsx ecx, WORD PTR [rbp-90]
__sbr_cell_37_347_end:
__sbr_cell_37_348:
    add edx, ecx
__sbr_cell_37_348_end:
sbr_reset.L15fb:
__sbr_cell_37_349:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_349_end:
__sbr_cell_37_350:
    cmp al, 13
__sbr_cell_37_350_end:
__sbr_cell_37_351:
    jb sbr_reset.L1622
__sbr_cell_37_351_end:
__sbr_cell_37_352:
    movsx ecx, WORD PTR [rbp-88]
__sbr_cell_37_352_end:
__sbr_cell_37_353:
    add edx, ecx
__sbr_cell_37_353_end:
__sbr_cell_37_354:
    mov DWORD PTR [r12+72], edx
__sbr_cell_37_354_end:
__sbr_cell_37_355:
    cmp al, 13
__sbr_cell_37_355_end:
__sbr_cell_37_356:
    je sbr_reset.L1622
__sbr_cell_37_356_end:
__sbr_cell_37_357:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_357_end:
sbr_reset.L1618:
__sbr_cell_37_358:
    mov edx, DWORD PTR [r12+72]
__sbr_cell_37_358_end:
__sbr_cell_37_359:
    jmp sbr_reset.L1622
__sbr_cell_37_359_end:
sbr_reset.L161f:
__sbr_cell_37_360:
    lea edx, [rdx+rdx*2+0]
__sbr_cell_37_360_end:
sbr_reset.L1622:
__sbr_cell_37_361:
    cmp edx, 64
__sbr_cell_37_361_end:
__sbr_cell_37_362:
    mov esi, 64
__sbr_cell_37_362_end:
__sbr_cell_37_363:
    cmovb esi, edx
__sbr_cell_37_363_end:
__sbr_cell_37_364:
    mov DWORD PTR [r12+72], esi
__sbr_cell_37_364_end:
__sbr_cell_37_365:
    mov ecx, DWORD PTR [r12+0]
__sbr_cell_37_365_end:
__sbr_cell_37_366:
    mov eax, 48
__sbr_cell_37_366_end:
__sbr_cell_37_367:
    cmp ecx, 32001
__sbr_cell_37_367_end:
__sbr_cell_37_368:
    jl sbr_reset.L1661
__sbr_cell_37_368_end:
__sbr_cell_37_369:
    mov eax, 35
__sbr_cell_37_369_end:
__sbr_cell_37_370:
    cmp ecx, 44100
__sbr_cell_37_370_end:
__sbr_cell_37_371:
    je sbr_reset.L1661
__sbr_cell_37_371_end:
__sbr_cell_37_372:
    mov eax, 32
__sbr_cell_37_372_end:
sbr_reset.L1655:
__sbr_cell_37_373:
    cmp ecx, 47999
__sbr_cell_37_373_end:
__sbr_cell_37_374:
    jbe sbr_reset.L328e
__sbr_cell_37_374_end:
sbr_reset.L1661:
__sbr_cell_37_375:
    mov r13d, DWORD PTR [r12+64]
__sbr_cell_37_375_end:
__sbr_cell_37_376:
    mov ecx, esi
__sbr_cell_37_376_end:
__sbr_cell_37_377:
    sub ecx, r13d
__sbr_cell_37_377_end:
__sbr_cell_37_378:
    cmp ecx, eax
__sbr_cell_37_378_end:
__sbr_cell_37_379:
    jbe sbr_reset.L1684
__sbr_cell_37_379_end:
__sbr_cell_37_380:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_380_end:
__sbr_cell_37_381:
    lea rdx, [rip+L_str_10]
__sbr_cell_37_381_end:
sbr_reset.L167a:
__sbr_cell_37_382:
    mov esi, 16
__sbr_cell_37_382_end:
__sbr_cell_37_383:
    jmp sbr_reset.L1d2a
__sbr_cell_37_383_end:
sbr_reset.L1684:
__sbr_cell_37_384:
    movzx eax, BYTE PTR [r12+31]
__sbr_cell_37_384_end:
__sbr_cell_37_385:
    test eax, eax
__sbr_cell_37_385_end:
__sbr_cell_37_386:
    je sbr_reset.L1779
__sbr_cell_37_386_end:
__sbr_cell_37_387:
    mov ecx, 7
__sbr_cell_37_387_end:
__sbr_cell_37_388:
    sub ecx, eax
__sbr_cell_37_388_end:
__sbr_cell_37_389:
    imul eax, esi, 49
__sbr_cell_37_389_end:
__sbr_cell_37_390:
    imul edx, r13d, 110
__sbr_cell_37_390_end:
__sbr_cell_37_391:
    lea r14d, [r13*2+0]
__sbr_cell_37_391_end:
__sbr_cell_37_392:
    mov DWORD PTR [rbp-128], eax
__sbr_cell_37_392_end:
__sbr_cell_37_393:
    mov DWORD PTR [rbp-136], edx
__sbr_cell_37_393_end:
__sbr_cell_37_394:
    cmp eax, edx
__sbr_cell_37_394_end:
__sbr_cell_37_395:
    cmovbe r14d, esi
__sbr_cell_37_395_end:
sbr_reset.L16b7:
__sbr_cell_37_396:
    mov DWORD PTR [r12+68], r14d
__sbr_cell_37_396_end:
__sbr_cell_37_397:
    vcvtsi2ss xmm0, xmm15, ecx
__sbr_cell_37_397_end:
__sbr_cell_37_398:
    vmovss DWORD PTR [rbp-56], xmm0
__sbr_cell_37_398_end:
__sbr_cell_37_399:
    vcvtsi2ss xmm0, xmm15, r14
__sbr_cell_37_399_end:
__sbr_cell_37_400:
    mov eax, r13d
__sbr_cell_37_400_end:
__sbr_cell_37_401:
    vcvtsi2ss xmm1, xmm15, rax
__sbr_cell_37_401_end:
__sbr_cell_37_402:
    vdivss xmm0, xmm0, xmm1
__sbr_cell_37_402_end:
sbr_reset.L16d6:
__sbr_cell_37_403:
    call log2f
__sbr_cell_37_403_end:
sbr_reset.L16db:
__sbr_cell_37_404:
    vmulss xmm0, xmm0, DWORD PTR [rbp-56]
__sbr_cell_37_404_end:
__sbr_cell_37_405:
    vcvtss2si rax, xmm0
__sbr_cell_37_405_end:
__sbr_cell_37_406:
    mov QWORD PTR [rbp-80], rax
__sbr_cell_37_406_end:
__sbr_cell_37_407:
    lea ecx, [rax+rax*1+0]
__sbr_cell_37_407_end:
__sbr_cell_37_408:
    test ecx, ecx
__sbr_cell_37_408_end:
__sbr_cell_37_409:
    jle sbr_reset.L17e7
__sbr_cell_37_409_end:
__sbr_cell_37_410:
    mov QWORD PTR [rbp-64], r15
__sbr_cell_37_410_end:
sbr_reset.L16f8:
__sbr_cell_37_411:
    mov QWORD PTR [rbp-48], r12
__sbr_cell_37_411_end:
__sbr_cell_37_412:
    vcvtsi2ss xmm0, xmm15, r14d
__sbr_cell_37_412_end:
__sbr_cell_37_413:
    vcvtsi2ss xmm2, xmm15, r13d
__sbr_cell_37_413_end:
__sbr_cell_37_414:
    vcvtsi2ss xmm1, xmm15, ecx
__sbr_cell_37_414_end:
__sbr_cell_37_415:
    vblendps xmm0, xmm0, XMMWORD PTR [rip+LCPI5_2], 14
__sbr_cell_37_415_end:
__sbr_cell_37_416:
    mov WORD PTR [rbp-368], 0
__sbr_cell_37_416_end:
sbr_reset.L171d:
__sbr_cell_37_417:
    vmovaps XMMWORD PTR [rbp-256], xmm2
__sbr_cell_37_417_end:
__sbr_cell_37_418:
    vinsertps xmm1, xmm2, xmm1, 16
__sbr_cell_37_418_end:
__sbr_cell_37_419:
    vdivps xmm0, xmm0, xmm1
__sbr_cell_37_419_end:
__sbr_cell_37_420:
    vmovshdup xmm1, xmm0
__sbr_cell_37_420_end:
__sbr_cell_37_421:
    mov rbx, rcx
__sbr_cell_37_421_end:
sbr_reset.L1736:
__sbr_cell_37_422:
    call powf
__sbr_cell_37_422_end:
sbr_reset.L173b:
__sbr_cell_37_423:
    lea eax, [rbx-1]
__sbr_cell_37_423_end:
__sbr_cell_37_424:
    mov QWORD PTR [rbp-72], rbx
__sbr_cell_37_424_end:
__sbr_cell_37_425:
    lea edx, [rbx-2]
__sbr_cell_37_425_end:
__sbr_cell_37_426:
    mov ecx, eax
__sbr_cell_37_426_end:
__sbr_cell_37_427:
    and ecx, 7
__sbr_cell_37_427_end:
__sbr_cell_37_428:
    cmp edx, 7
__sbr_cell_37_428_end:
__sbr_cell_37_429:
    jae sbr_reset.L1830
__sbr_cell_37_429_end:
__sbr_cell_37_430:
    xor edx, edx
__sbr_cell_37_430_end:
__sbr_cell_37_431:
    vmovaps xmm1, XMMWORD PTR [rbp-256]
__sbr_cell_37_431_end:
__sbr_cell_37_432:
    jmp sbr_reset.L1908
__sbr_cell_37_432_end:
sbr_reset.L1762:
__sbr_cell_37_433:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_433_end:
__sbr_cell_37_434:
    lea rdx, [rip+L_str_8]
__sbr_cell_37_434_end:
__sbr_cell_37_435:
    mov esi, 16
__sbr_cell_37_435_end:
__sbr_cell_37_436:
    mov ecx, eax
__sbr_cell_37_436_end:
__sbr_cell_37_437:
    jmp sbr_reset.L1d2a
__sbr_cell_37_437_end:
sbr_reset.L1779:
__sbr_cell_37_438:
    movzx eax, BYTE PTR [r12+32]
__sbr_cell_37_438_end:
__sbr_cell_37_439:
    inc eax
__sbr_cell_37_439_end:
__sbr_cell_37_440:
    mov edx, eax
__sbr_cell_37_440_end:
__sbr_cell_37_441:
    and edx, 2
__sbr_cell_37_441_end:
__sbr_cell_37_442:
    add edx, ecx
__sbr_cell_37_442_end:
__sbr_cell_37_443:
    mov ecx, eax
__sbr_cell_37_443_end:
__sbr_cell_37_444:
    shr edx, cl
__sbr_cell_37_444_end:
__sbr_cell_37_445:
    lea ecx, [rdx+rdx*1+0]
__sbr_cell_37_445_end:
__sbr_cell_37_446:
    mov DWORD PTR [r12+104], ecx
__sbr_cell_37_446_end:
__sbr_cell_37_447:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_447_end:
__sbr_cell_37_448:
    test edx, edx
__sbr_cell_37_448_end:
__sbr_cell_37_449:
    je sbr_reset.L1d0d
__sbr_cell_37_449_end:
sbr_reset.L17a0:
__sbr_cell_37_450:
    movzx r8d, BYTE PTR [r12+30]
__sbr_cell_37_450_end:
__sbr_cell_37_451:
    cmp ecx, r8d
__sbr_cell_37_451_end:
__sbr_cell_37_452:
    jbe sbr_reset.L1d1b
__sbr_cell_37_452_end:
__sbr_cell_37_453:
    lea edx, [rcx-1]
__sbr_cell_37_453_end:
__sbr_cell_37_454:
    cmp edx, 48
__sbr_cell_37_454_end:
__sbr_cell_37_455:
    mov edi, 48
__sbr_cell_37_455_end:
__sbr_cell_37_456:
    cmovb edi, edx
__sbr_cell_37_456_end:
__sbr_cell_37_457:
    cmp edi, 48
__sbr_cell_37_457_end:
__sbr_cell_37_458:
    je sbr_reset.L32d2
__sbr_cell_37_458_end:
__sbr_cell_37_459:
    mov edx, ecx
__sbr_cell_37_459_end:
__sbr_cell_37_460:
    mov edi, 1
__sbr_cell_37_460_end:
__sbr_cell_37_461:
    cmp ecx, 8
__sbr_cell_37_461_end:
__sbr_cell_37_462:
    jb sbr_reset.L1ea8
__sbr_cell_37_462_end:
sbr_reset.L17d6:
__sbr_cell_37_463:
    cmp ecx, 32
__sbr_cell_37_463_end:
__sbr_cell_37_464:
    jae sbr_reset.L1e09
__sbr_cell_37_464_end:
__sbr_cell_37_465:
    xor r8d, r8d
__sbr_cell_37_465_end:
__sbr_cell_37_466:
    jmp sbr_reset.L1e6b
__sbr_cell_37_466_end:
sbr_reset.L17e7:
__sbr_cell_37_467:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_467_end:
__sbr_cell_37_468:
    lea rdx, [rip+L_str_11]
__sbr_cell_37_468_end:
__sbr_cell_37_469:
    mov esi, 16
__sbr_cell_37_469_end:
__sbr_cell_37_470:
    jmp sbr_reset.L1d2a
__sbr_cell_37_470_end:
sbr_reset.L17fc:
__sbr_cell_37_471:
    lea rdi, [rip+sbr_offset_0]
__sbr_cell_37_471_end:
__sbr_cell_37_472:
    jmp sbr_reset.L114a
__sbr_cell_37_472_end:
sbr_reset.L1808:
__sbr_cell_37_473:
    lea rdi, [rip+sbr_offset_3]
__sbr_cell_37_473_end:
__sbr_cell_37_474:
    jmp sbr_reset.L114a
__sbr_cell_37_474_end:
sbr_reset.L1814:
__sbr_cell_37_475:
    lea rdi, [rip+sbr_offset_1]
__sbr_cell_37_475_end:
__sbr_cell_37_476:
    jmp sbr_reset.L114a
__sbr_cell_37_476_end:
sbr_reset.L1820:
__sbr_cell_37_477:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_477_end:
__sbr_cell_37_478:
    lea rdx, [rip+L_str_7]
__sbr_cell_37_478_end:
__sbr_cell_37_479:
    jmp sbr_reset.L167a
__sbr_cell_37_479_end:
sbr_reset.L1830:
__sbr_cell_37_480:
    mov esi, eax
__sbr_cell_37_480_end:
__sbr_cell_37_481:
    and esi, 2147483640
__sbr_cell_37_481_end:
__sbr_cell_37_482:
    xor edx, edx
__sbr_cell_37_482_end:
__sbr_cell_37_483:
    vmovaps xmm1, XMMWORD PTR [rbp-256]
__sbr_cell_37_483_end:
__sbr_cell_37_484:
    .nops 1
__sbr_cell_37_484_end:
sbr_reset.L1850:
__sbr_cell_37_485:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_485_end:
__sbr_cell_37_486:
    vcvtss2si rdi, xmm1
__sbr_cell_37_486_end:
__sbr_cell_37_487:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_487_end:
__sbr_cell_37_488:
    vcvtss2si r8, xmm1
__sbr_cell_37_488_end:
__sbr_cell_37_489:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_489_end:
__sbr_cell_37_490:
    vcvtss2si r9, xmm1
__sbr_cell_37_490_end:
__sbr_cell_37_491:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_491_end:
__sbr_cell_37_492:
    vcvtss2si r10, xmm1
__sbr_cell_37_492_end:
__sbr_cell_37_493:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_493_end:
__sbr_cell_37_494:
    vcvtss2si r11, xmm1
__sbr_cell_37_494_end:
__sbr_cell_37_495:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_495_end:
__sbr_cell_37_496:
    vcvtss2si rbx, xmm1
__sbr_cell_37_496_end:
sbr_reset.L1886:
__sbr_cell_37_497:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_497_end:
__sbr_cell_37_498:
    vcvtss2si r12, xmm1
__sbr_cell_37_498_end:
__sbr_cell_37_499:
    mov r15d, r12d
__sbr_cell_37_499_end:
__sbr_cell_37_500:
    sub r15d, ebx
__sbr_cell_37_500_end:
__sbr_cell_37_501:
    sub ebx, r11d
__sbr_cell_37_501_end:
__sbr_cell_37_502:
    sub r11d, r10d
__sbr_cell_37_502_end:
__sbr_cell_37_503:
    sub r10d, r9d
__sbr_cell_37_503_end:
__sbr_cell_37_504:
    sub r9d, r8d
__sbr_cell_37_504_end:
__sbr_cell_37_505:
    sub r8d, edi
__sbr_cell_37_505_end:
__sbr_cell_37_506:
    sub edi, r13d
__sbr_cell_37_506_end:
__sbr_cell_37_507:
    mov WORD PTR [rbp+rdx*2-366], di
__sbr_cell_37_507_end:
__sbr_cell_37_508:
    mov WORD PTR [rbp+rdx*2-364], r8w
__sbr_cell_37_508_end:
sbr_reset.L18b8:
__sbr_cell_37_509:
    mov WORD PTR [rbp+rdx*2-362], r9w
__sbr_cell_37_509_end:
__sbr_cell_37_510:
    mov WORD PTR [rbp+rdx*2-360], r10w
__sbr_cell_37_510_end:
sbr_reset.L18ca:
__sbr_cell_37_511:
    mov WORD PTR [rbp+rdx*2-358], r11w
__sbr_cell_37_511_end:
__sbr_cell_37_512:
    mov WORD PTR [rbp+rdx*2-356], bx
__sbr_cell_37_512_end:
sbr_reset.L18db:
__sbr_cell_37_513:
    mov WORD PTR [rbp+rdx*2-354], r15w
__sbr_cell_37_513_end:
__sbr_cell_37_514:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_514_end:
__sbr_cell_37_515:
    vcvtss2si r13, xmm1
__sbr_cell_37_515_end:
__sbr_cell_37_516:
    mov edi, r13d
__sbr_cell_37_516_end:
__sbr_cell_37_517:
    sub edi, r12d
__sbr_cell_37_517_end:
__sbr_cell_37_518:
    mov WORD PTR [rbp+rdx*2-352], di
__sbr_cell_37_518_end:
__sbr_cell_37_519:
    add rdx, 8
__sbr_cell_37_519_end:
__sbr_cell_37_520:
    cmp rsi, rdx
__sbr_cell_37_520_end:
__sbr_cell_37_521:
    jne sbr_reset.L1850
__sbr_cell_37_521_end:
sbr_reset.L1908:
__sbr_cell_37_522:
    lea rsi, [rbp-366]
__sbr_cell_37_522_end:
__sbr_cell_37_523:
    lea rdx, [rdx*2-366]
__sbr_cell_37_523_end:
__sbr_cell_37_524:
    add rdx, rbp
__sbr_cell_37_524_end:
__sbr_cell_37_525:
    xor edi, edi
__sbr_cell_37_525_end:
__sbr_cell_37_526:
    .nops 1
__sbr_cell_37_526_end:
sbr_reset.L1920:
__sbr_cell_37_527:
    mov r8d, r13d
__sbr_cell_37_527_end:
__sbr_cell_37_528:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_528_end:
__sbr_cell_37_529:
    vcvtss2si r13, xmm1
__sbr_cell_37_529_end:
__sbr_cell_37_530:
    mov r9d, r13d
__sbr_cell_37_530_end:
__sbr_cell_37_531:
    sub r9d, r8d
__sbr_cell_37_531_end:
__sbr_cell_37_532:
    mov WORD PTR [rdx+rdi*2+0], r9w
__sbr_cell_37_532_end:
__sbr_cell_37_533:
    inc rdi
__sbr_cell_37_533_end:
__sbr_cell_37_534:
    cmp rcx, rdi
__sbr_cell_37_534_end:
__sbr_cell_37_535:
    jne sbr_reset.L1920
__sbr_cell_37_535_end:
__sbr_cell_37_536:
    sub r14d, r13d
__sbr_cell_37_536_end:
__sbr_cell_37_537:
    mov WORD PTR [rbp+rax*2-366], r14w
__sbr_cell_37_537_end:
sbr_reset.L194b:
__sbr_cell_37_538:
    mov QWORD PTR [rbp-1392], rsi
__sbr_cell_37_538_end:
__sbr_cell_37_539:
    mov eax, DWORD PTR [rbp-72]
__sbr_cell_37_539_end:
__sbr_cell_37_540:
    lea rcx, [rsi+rax*2+0]
__sbr_cell_37_540_end:
__sbr_cell_37_541:
    add rcx, -2
__sbr_cell_37_541_end:
__sbr_cell_37_542:
    mov QWORD PTR [rbp-1384], rcx
__sbr_cell_37_542_end:
__sbr_cell_37_543:
    mov ecx, 1
__sbr_cell_37_543_end:
__sbr_cell_37_544:
    mov r12, QWORD PTR [rbp-48]
__sbr_cell_37_544_end:
__sbr_cell_37_545:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_545_end:
__sbr_cell_37_546:
    jmp sbr_reset.L1988
__sbr_cell_37_546_end:
__sbr_cell_37_547:
    .nops 1
__sbr_cell_37_547_end:
sbr_reset.L1980:
__sbr_cell_37_548:
    test ecx, ecx
__sbr_cell_37_548_end:
__sbr_cell_37_549:
    je sbr_reset.L1bbd
__sbr_cell_37_549_end:
sbr_reset.L1988:
__sbr_cell_37_550:
    cmp ecx, 65
__sbr_cell_37_550_end:
__sbr_cell_37_551:
    jae sbr_reset.L3266
__sbr_cell_37_551_end:
__sbr_cell_37_552:
    dec ecx
__sbr_cell_37_552_end:
__sbr_cell_37_553:
    mov rdx, rcx
__sbr_cell_37_553_end:
__sbr_cell_37_554:
    shl rdx, 4
__sbr_cell_37_554_end:
__sbr_cell_37_555:
    mov rsi, QWORD PTR [rbp+rdx*1-1392]
__sbr_cell_37_555_end:
__sbr_cell_37_556:
    mov rdx, QWORD PTR [rbp+rdx*1-1384]
__sbr_cell_37_556_end:
__sbr_cell_37_557:
    .nops 1
__sbr_cell_37_557_end:
sbr_reset.L19b0:
__sbr_cell_37_558:
    cmp rsi, rdx
__sbr_cell_37_558_end:
__sbr_cell_37_559:
    jae sbr_reset.L1980
__sbr_cell_37_559_end:
__sbr_cell_37_560:
    lea r8, [rdx-2]
__sbr_cell_37_560_end:
__sbr_cell_37_561:
    cmp rsi, r8
__sbr_cell_37_561_end:
__sbr_cell_37_562:
    jae sbr_reset.L1ba0
__sbr_cell_37_562_end:
__sbr_cell_37_563:
    mov r9, rdx
__sbr_cell_37_563_end:
__sbr_cell_37_564:
    sub r9, rsi
__sbr_cell_37_564_end:
__sbr_cell_37_565:
    sar r9, 2
__sbr_cell_37_565_end:
__sbr_cell_37_566:
    lea rdi, [rsi+r9*2+0]
__sbr_cell_37_566_end:
__sbr_cell_37_567:
    movzx r10d, WORD PTR [rsi+0]
__sbr_cell_37_567_end:
__sbr_cell_37_568:
    movzx r14d, WORD PTR [rdx+0]
__sbr_cell_37_568_end:
__sbr_cell_37_569:
    movzx r9d, WORD PTR [rsi+r9*2+0]
__sbr_cell_37_569_end:
sbr_reset.L19dd:
__sbr_cell_37_570:
    cmp r10w, r14w
__sbr_cell_37_570_end:
__sbr_cell_37_571:
    jle sbr_reset.L1a00
__sbr_cell_37_571_end:
__sbr_cell_37_572:
    cmp r14w, r9w
__sbr_cell_37_572_end:
__sbr_cell_37_573:
    jg sbr_reset.L1a0c
__sbr_cell_37_573_end:
__sbr_cell_37_574:
    mov WORD PTR [rdx+0], r10w
__sbr_cell_37_574_end:
__sbr_cell_37_575:
    mov r9d, r14d
__sbr_cell_37_575_end:
__sbr_cell_37_576:
    jmp sbr_reset.L1a10
__sbr_cell_37_576_end:
__sbr_cell_37_577:
    .nops 1
__sbr_cell_37_577_end:
sbr_reset.L1a00:
__sbr_cell_37_578:
    mov r11d, 1
__sbr_cell_37_578_end:
__sbr_cell_37_579:
    cmp r10w, r9w
__sbr_cell_37_579_end:
__sbr_cell_37_580:
    jle sbr_reset.L1a1f
__sbr_cell_37_580_end:
sbr_reset.L1a0c:
__sbr_cell_37_581:
    mov WORD PTR [rdi+0], r10w
__sbr_cell_37_581_end:
sbr_reset.L1a10:
__sbr_cell_37_582:
    mov WORD PTR [rsi+0], r9w
__sbr_cell_37_582_end:
__sbr_cell_37_583:
    movzx r9d, WORD PTR [rdi+0]
__sbr_cell_37_583_end:
__sbr_cell_37_584:
    movzx r14d, WORD PTR [rdx+0]
__sbr_cell_37_584_end:
__sbr_cell_37_585:
    xor r11d, r11d
__sbr_cell_37_585_end:
sbr_reset.L1a1f:
__sbr_cell_37_586:
    cmp r9w, r14w
__sbr_cell_37_586_end:
__sbr_cell_37_587:
    jle sbr_reset.L1a40
__sbr_cell_37_587_end:
__sbr_cell_37_588:
    mov WORD PTR [rdx+0], r9w
__sbr_cell_37_588_end:
__sbr_cell_37_589:
    mov WORD PTR [rdi+0], r14w
__sbr_cell_37_589_end:
__sbr_cell_37_590:
    xor r11d, r11d
__sbr_cell_37_590_end:
__sbr_cell_37_591:
    lea r9, [rdx-4]
__sbr_cell_37_591_end:
__sbr_cell_37_592:
    cmp rsi, r9
__sbr_cell_37_592_end:
__sbr_cell_37_593:
    jne sbr_reset.L1a50
__sbr_cell_37_593_end:
__sbr_cell_37_594:
    jmp sbr_reset.L1980
__sbr_cell_37_594_end:
__sbr_cell_37_595:
    .nops 1
__sbr_cell_37_595_end:
sbr_reset.L1a40:
__sbr_cell_37_596:
    mov r14d, r9d
__sbr_cell_37_596_end:
__sbr_cell_37_597:
    lea r9, [rdx-4]
__sbr_cell_37_597_end:
__sbr_cell_37_598:
    cmp rsi, r9
__sbr_cell_37_598_end:
__sbr_cell_37_599:
    je sbr_reset.L1980
__sbr_cell_37_599_end:
sbr_reset.L1a50:
__sbr_cell_37_600:
    lea r10, [rsi+2]
__sbr_cell_37_600_end:
__sbr_cell_37_601:
    movzx ebx, WORD PTR [r8+0]
__sbr_cell_37_601_end:
__sbr_cell_37_602:
    mov WORD PTR [rdi+0], bx
__sbr_cell_37_602_end:
__sbr_cell_37_603:
    mov WORD PTR [r8+0], r14w
__sbr_cell_37_603_end:
__sbr_cell_37_604:
    cmp r10, r9
__sbr_cell_37_604_end:
__sbr_cell_37_605:
    jbe sbr_reset.L1a89
__sbr_cell_37_605_end:
__sbr_cell_37_606:
    jmp sbr_reset.L1ad4
__sbr_cell_37_606_end:
__sbr_cell_37_607:
    .nops 1
__sbr_cell_37_607_end:
sbr_reset.L1a70:
__sbr_cell_37_608:
    movzx ebx, WORD PTR [r10+0]
__sbr_cell_37_608_end:
__sbr_cell_37_609:
    mov WORD PTR [r9+0], bx
__sbr_cell_37_609_end:
__sbr_cell_37_610:
    mov WORD PTR [r10+0], r13w
__sbr_cell_37_610_end:
__sbr_cell_37_611:
    add r10, 2
__sbr_cell_37_611_end:
__sbr_cell_37_612:
    add r9, -2
__sbr_cell_37_612_end:
sbr_reset.L1a84:
__sbr_cell_37_613:
    cmp r10, r9
__sbr_cell_37_613_end:
__sbr_cell_37_614:
    ja sbr_reset.L1ad0
__sbr_cell_37_614_end:
sbr_reset.L1a89:
__sbr_cell_37_615:
    movzx r14d, WORD PTR [r8+0]
__sbr_cell_37_615_end:
__sbr_cell_37_616:
    .nops 1
__sbr_cell_37_616_end:
sbr_reset.L1a90:
__sbr_cell_37_617:
    cmp WORD PTR [r10+0], r14w
__sbr_cell_37_617_end:
__sbr_cell_37_618:
    jge sbr_reset.L1ab4
__sbr_cell_37_618_end:
__sbr_cell_37_619:
    add r10, 2
__sbr_cell_37_619_end:
__sbr_cell_37_620:
    cmp r10, r9
__sbr_cell_37_620_end:
__sbr_cell_37_621:
    jbe sbr_reset.L1a90
__sbr_cell_37_621_end:
__sbr_cell_37_622:
    jmp sbr_reset.L1ab4
__sbr_cell_37_622_end:
__sbr_cell_37_623:
    .nops 1
__sbr_cell_37_623_end:
sbr_reset.L1ab0:
__sbr_cell_37_624:
    add r9, -2
__sbr_cell_37_624_end:
sbr_reset.L1ab4:
__sbr_cell_37_625:
    cmp r10, r9
__sbr_cell_37_625_end:
__sbr_cell_37_626:
    ja sbr_reset.L1a84
__sbr_cell_37_626_end:
__sbr_cell_37_627:
    movzx r13d, WORD PTR [r9+0]
__sbr_cell_37_627_end:
__sbr_cell_37_628:
    cmp r13w, r14w
__sbr_cell_37_628_end:
__sbr_cell_37_629:
    jg sbr_reset.L1ab0
__sbr_cell_37_629_end:
__sbr_cell_37_630:
    jmp sbr_reset.L1a70
__sbr_cell_37_630_end:
__sbr_cell_37_631:
    .nops 1
__sbr_cell_37_631_end:
sbr_reset.L1ad0:
__sbr_cell_37_632:
    movzx r14d, WORD PTR [r8+0]
__sbr_cell_37_632_end:
sbr_reset.L1ad4:
__sbr_cell_37_633:
    movzx ebx, WORD PTR [r10+0]
__sbr_cell_37_633_end:
__sbr_cell_37_634:
    mov WORD PTR [r10+0], r14w
__sbr_cell_37_634_end:
__sbr_cell_37_635:
    mov WORD PTR [r8+0], bx
__sbr_cell_37_635_end:
__sbr_cell_37_636:
    test r11d, r11d
__sbr_cell_37_636_end:
__sbr_cell_37_637:
    je sbr_reset.L1b20
__sbr_cell_37_637_end:
__sbr_cell_37_638:
    cmp rdi, r10
__sbr_cell_37_638_end:
__sbr_cell_37_639:
    je sbr_reset.L1af3
__sbr_cell_37_639_end:
__sbr_cell_37_640:
    lea r8, [r10-2]
__sbr_cell_37_640_end:
__sbr_cell_37_641:
    cmp rdi, r8
__sbr_cell_37_641_end:
__sbr_cell_37_642:
    jne sbr_reset.L1b20
__sbr_cell_37_642_end:
sbr_reset.L1af3:
__sbr_cell_37_643:
    mov r8, rsi
__sbr_cell_37_643_end:
__sbr_cell_37_644:
    .nops 1
__sbr_cell_37_644_end:
sbr_reset.L1b00:
__sbr_cell_37_645:
    mov rdi, r8
__sbr_cell_37_645_end:
__sbr_cell_37_646:
    cmp r8, rdx
__sbr_cell_37_646_end:
__sbr_cell_37_647:
    jae sbr_reset.L1b17
__sbr_cell_37_647_end:
__sbr_cell_37_648:
    lea r8, [rdi+2]
__sbr_cell_37_648_end:
__sbr_cell_37_649:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_649_end:
__sbr_cell_37_650:
    cmp r11w, WORD PTR [rdi+2]
__sbr_cell_37_650_end:
__sbr_cell_37_651:
    jle sbr_reset.L1b00
__sbr_cell_37_651_end:
sbr_reset.L1b17:
__sbr_cell_37_652:
    cmp rdi, rdx
__sbr_cell_37_652_end:
__sbr_cell_37_653:
    je sbr_reset.L1980
__sbr_cell_37_653_end:
sbr_reset.L1b20:
__sbr_cell_37_654:
    mov rdi, rdx
__sbr_cell_37_654_end:
__sbr_cell_37_655:
    sub rdi, r10
__sbr_cell_37_655_end:
__sbr_cell_37_656:
    mov r8, r10
__sbr_cell_37_656_end:
__sbr_cell_37_657:
    sub r8, rsi
__sbr_cell_37_657_end:
__sbr_cell_37_658:
    cmp rdi, r8
__sbr_cell_37_658_end:
__sbr_cell_37_659:
    jge sbr_reset.L1b70
__sbr_cell_37_659_end:
__sbr_cell_37_660:
    cmp rcx, 64
__sbr_cell_37_660_end:
__sbr_cell_37_661:
    jae sbr_reset.L325c
__sbr_cell_37_661_end:
__sbr_cell_37_662:
    mov rdi, rcx
__sbr_cell_37_662_end:
__sbr_cell_37_663:
    shl rdi, 4
__sbr_cell_37_663_end:
__sbr_cell_37_664:
    mov QWORD PTR [rbp+rdi*1-1392], rsi
__sbr_cell_37_664_end:
__sbr_cell_37_665:
    mov QWORD PTR [rbp+rdi*1-1384], r9
__sbr_cell_37_665_end:
sbr_reset.L1b52:
__sbr_cell_37_666:
    add r10, 2
__sbr_cell_37_666_end:
__sbr_cell_37_667:
    mov rsi, r10
__sbr_cell_37_667_end:
__sbr_cell_37_668:
    inc rcx
__sbr_cell_37_668_end:
__sbr_cell_37_669:
    jmp sbr_reset.L19b0
__sbr_cell_37_669_end:
__sbr_cell_37_670:
    .nops 1
__sbr_cell_37_670_end:
sbr_reset.L1b70:
__sbr_cell_37_671:
    cmp rcx, 64
__sbr_cell_37_671_end:
__sbr_cell_37_672:
    jae sbr_reset.L3261
__sbr_cell_37_672_end:
__sbr_cell_37_673:
    add r10, 2
__sbr_cell_37_673_end:
__sbr_cell_37_674:
    mov rdi, rcx
__sbr_cell_37_674_end:
__sbr_cell_37_675:
    shl rdi, 4
__sbr_cell_37_675_end:
__sbr_cell_37_676:
    mov QWORD PTR [rbp+rdi*1-1392], r10
__sbr_cell_37_676_end:
__sbr_cell_37_677:
    mov QWORD PTR [rbp+rdi*1-1384], rdx
__sbr_cell_37_677_end:
__sbr_cell_37_678:
    mov rdx, r9
__sbr_cell_37_678_end:
__sbr_cell_37_679:
    inc rcx
__sbr_cell_37_679_end:
__sbr_cell_37_680:
    jmp sbr_reset.L19b0
__sbr_cell_37_680_end:
sbr_reset.L1ba0:
__sbr_cell_37_681:
    movzx edi, WORD PTR [rsi+0]
__sbr_cell_37_681_end:
__sbr_cell_37_682:
    movzx r8d, WORD PTR [rdx+0]
__sbr_cell_37_682_end:
__sbr_cell_37_683:
    cmp di, r8w
__sbr_cell_37_683_end:
__sbr_cell_37_684:
    jle sbr_reset.L1980
__sbr_cell_37_684_end:
__sbr_cell_37_685:
    mov WORD PTR [rdx+0], di
__sbr_cell_37_685_end:
__sbr_cell_37_686:
    mov WORD PTR [rsi+0], r8w
__sbr_cell_37_686_end:
__sbr_cell_37_687:
    jmp sbr_reset.L1980
__sbr_cell_37_687_end:
sbr_reset.L1bbd:
__sbr_cell_37_688:
    mov rcx, QWORD PTR [rbp-72]
__sbr_cell_37_688_end:
__sbr_cell_37_689:
    cmp ecx, 49
__sbr_cell_37_689_end:
__sbr_cell_37_690:
    jae sbr_reset.L32be
__sbr_cell_37_690_end:
__sbr_cell_37_691:
    movsx edi, WORD PTR [rbp+rax*2-368]
__sbr_cell_37_691_end:
__sbr_cell_37_692:
    movzx eax, WORD PTR [r12+64]
__sbr_cell_37_692_end:
__sbr_cell_37_693:
    mov WORD PTR [rbp-368], ax
__sbr_cell_37_693_end:
__sbr_cell_37_694:
    lea esi, [rcx+1]
__sbr_cell_37_694_end:
__sbr_cell_37_695:
    mov rax, QWORD PTR [rbp-80]
__sbr_cell_37_695_end:
__sbr_cell_37_696:
    add eax, eax
__sbr_cell_37_696_end:
__sbr_cell_37_697:
    neg rax
__sbr_cell_37_697_end:
__sbr_cell_37_698:
    mov ecx, 1
__sbr_cell_37_698_end:
sbr_reset.L1bf0:
__sbr_cell_37_699:
    movsx r8d, WORD PTR [rbp+rcx*2-368]
__sbr_cell_37_699_end:
__sbr_cell_37_700:
    test r8d, r8d
__sbr_cell_37_700_end:
__sbr_cell_37_701:
    jle sbr_reset.L1cf4
__sbr_cell_37_701_end:
__sbr_cell_37_702:
    add r8w, WORD PTR [rbp+rcx*2-370]
__sbr_cell_37_702_end:
__sbr_cell_37_703:
    mov WORD PTR [rbp+rcx*2-368], r8w
__sbr_cell_37_703_end:
__sbr_cell_37_704:
    lea rdx, [rax+rcx*1+0]
__sbr_cell_37_704_end:
__sbr_cell_37_705:
    inc rdx
__sbr_cell_37_705_end:
__sbr_cell_37_706:
    inc rcx
__sbr_cell_37_706_end:
__sbr_cell_37_707:
    cmp rdx, 1
__sbr_cell_37_707_end:
__sbr_cell_37_708:
    jne sbr_reset.L1bf0
__sbr_cell_37_708_end:
__sbr_cell_37_709:
    mov eax, DWORD PTR [rbp-136]
__sbr_cell_37_709_end:
__sbr_cell_37_710:
    cmp DWORD PTR [rbp-128], eax
__sbr_cell_37_710_end:
__sbr_cell_37_711:
    jbe sbr_reset.L1da7
__sbr_cell_37_711_end:
sbr_reset.L1c33:
__sbr_cell_37_712:
    mov DWORD PTR [rbp-80], edi
__sbr_cell_37_712_end:
__sbr_cell_37_713:
    mov QWORD PTR [rbp-136], rsi
__sbr_cell_37_713_end:
__sbr_cell_37_714:
    xor eax, eax
__sbr_cell_37_714_end:
__sbr_cell_37_715:
    cmp BYTE PTR [r12+32], 0
__sbr_cell_37_715_end:
__sbr_cell_37_716:
    sete al
__sbr_cell_37_716_end:
__sbr_cell_37_717:
    lea rcx, [rip+LCPI5_3]
__sbr_cell_37_717_end:
__sbr_cell_37_718:
    vmovss xmm0, DWORD PTR [rbp-56]
__sbr_cell_37_718_end:
__sbr_cell_37_719:
    vmulss xmm0, xmm0, DWORD PTR [rcx+rax*4+0]
__sbr_cell_37_719_end:
sbr_reset.L1c59:
__sbr_cell_37_720:
    vmovss DWORD PTR [rbp-56], xmm0
__sbr_cell_37_720_end:
__sbr_cell_37_721:
    mov r13d, DWORD PTR [r12+68]
__sbr_cell_37_721_end:
__sbr_cell_37_722:
    mov r14d, DWORD PTR [r12+72]
__sbr_cell_37_722_end:
__sbr_cell_37_723:
    vcvtsi2ss xmm0, xmm15, r14
__sbr_cell_37_723_end:
__sbr_cell_37_724:
    vcvtsi2ss xmm1, xmm15, r13
__sbr_cell_37_724_end:
__sbr_cell_37_725:
    vdivss xmm0, xmm0, xmm1
__sbr_cell_37_725_end:
sbr_reset.L1c76:
__sbr_cell_37_726:
    call log2f
__sbr_cell_37_726_end:
sbr_reset.L1c7b:
__sbr_cell_37_727:
    vmulss xmm0, xmm0, DWORD PTR [rbp-56]
__sbr_cell_37_727_end:
__sbr_cell_37_728:
    vcvtss2si r15, xmm0
__sbr_cell_37_728_end:
__sbr_cell_37_729:
    lea ebx, [r15+r15*1+0]
__sbr_cell_37_729_end:
__sbr_cell_37_730:
    vcvtsi2ss xmm0, xmm15, r14d
__sbr_cell_37_730_end:
__sbr_cell_37_731:
    vmovd xmm1, r13d
__sbr_cell_37_731_end:
__sbr_cell_37_732:
    vpinsrd xmm1, xmm1, ebx, 1
__sbr_cell_37_732_end:
__sbr_cell_37_733:
    vcvtdq2ps xmm1, xmm1
__sbr_cell_37_733_end:
__sbr_cell_37_734:
    vblendps xmm0, xmm0, XMMWORD PTR [rip+LCPI5_2], 14
__sbr_cell_37_734_end:
__sbr_cell_37_735:
    vmovaps XMMWORD PTR [rbp-128], xmm1
__sbr_cell_37_735_end:
__sbr_cell_37_736:
    vdivps xmm0, xmm0, xmm1
__sbr_cell_37_736_end:
__sbr_cell_37_737:
    vmovshdup xmm1, xmm0
__sbr_cell_37_737_end:
sbr_reset.L1cb4:
__sbr_cell_37_738:
    call powf
__sbr_cell_37_738_end:
sbr_reset.L1cb9:
__sbr_cell_37_739:
    lea eax, [r15*2-1]
__sbr_cell_37_739_end:
__sbr_cell_37_740:
    cmp ebx, 2
__sbr_cell_37_740_end:
__sbr_cell_37_741:
    jl sbr_reset.L1de3
__sbr_cell_37_741_end:
__sbr_cell_37_742:
    mov eax, eax
__sbr_cell_37_742_end:
__sbr_cell_37_743:
    mov QWORD PTR [rbp-56], rbx
__sbr_cell_37_743_end:
__sbr_cell_37_744:
    lea edx, [rbx-2]
__sbr_cell_37_744_end:
__sbr_cell_37_745:
    mov ecx, eax
__sbr_cell_37_745_end:
__sbr_cell_37_746:
    and ecx, 7
__sbr_cell_37_746_end:
__sbr_cell_37_747:
    cmp edx, 7
__sbr_cell_37_747_end:
__sbr_cell_37_748:
    mov QWORD PTR [rbp-256], rax
__sbr_cell_37_748_end:
__sbr_cell_37_749:
    jae sbr_reset.L2112
__sbr_cell_37_749_end:
__sbr_cell_37_750:
    xor edx, edx
__sbr_cell_37_750_end:
sbr_reset.L1cea:
__sbr_cell_37_751:
    vmovaps xmm1, XMMWORD PTR [rbp-128]
__sbr_cell_37_751_end:
__sbr_cell_37_752:
    jmp sbr_reset.L21e6
__sbr_cell_37_752_end:
sbr_reset.L1cf4:
__sbr_cell_37_753:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_753_end:
__sbr_cell_37_754:
    lea rdx, [rip+L_str_12]
__sbr_cell_37_754_end:
sbr_reset.L1cff:
__sbr_cell_37_755:
    mov esi, 16
__sbr_cell_37_755_end:
__sbr_cell_37_756:
    xor eax, eax
__sbr_cell_37_756_end:
__sbr_cell_37_757:
    call av_log
__sbr_cell_37_757_end:
sbr_reset.L1d0b:
__sbr_cell_37_758:
    jmp sbr_reset.L1d31
__sbr_cell_37_758_end:
sbr_reset.L1d0d:
__sbr_cell_37_759:
    lea rdx, [rip+L_str_14]
__sbr_cell_37_759_end:
__sbr_cell_37_760:
    mov esi, 16
__sbr_cell_37_760_end:
__sbr_cell_37_761:
    jmp sbr_reset.L1d2a
__sbr_cell_37_761_end:
sbr_reset.L1d1b:
__sbr_cell_37_762:
    lea rdx, [rip+L_str_15]
__sbr_cell_37_762_end:
__sbr_cell_37_763:
    mov esi, 16
__sbr_cell_37_763_end:
__sbr_cell_37_764:
    mov ecx, r8d
__sbr_cell_37_764_end:
sbr_reset.L1d2a:
__sbr_cell_37_765:
    xor eax, eax
__sbr_cell_37_765_end:
__sbr_cell_37_766:
    call av_log
__sbr_cell_37_766_end:
sbr_reset.L1d31:
__sbr_cell_37_767:
    lea rbx, [r12+28]
__sbr_cell_37_767_end:
__sbr_cell_37_768:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_768_end:
__sbr_cell_37_769:
    lea rdx, [rip+L_str_6]
__sbr_cell_37_769_end:
__sbr_cell_37_770:
    mov esi, 16
__sbr_cell_37_770_end:
__sbr_cell_37_771:
    xor eax, eax
__sbr_cell_37_771_end:
sbr_reset.L1d48:
__sbr_cell_37_772:
    call av_log
__sbr_cell_37_772_end:
sbr_reset.L1d4d:
__sbr_cell_37_773:
    mov QWORD PTR [r12+4], 0
__sbr_cell_37_773_end:
__sbr_cell_37_774:
    mov DWORD PTR [r12+16], 0
__sbr_cell_37_774_end:
sbr_reset.L1d5f:
__sbr_cell_37_775:
    mov DWORD PTR [r12+88], 32
__sbr_cell_37_775_end:
__sbr_cell_37_776:
    mov DWORD PTR [r12+96], 0
__sbr_cell_37_776_end:
sbr_reset.L1d71:
__sbr_cell_37_777:
    mov DWORD PTR [r12+103496], 4294967295
__sbr_cell_37_777_end:
__sbr_cell_37_778:
    mov DWORD PTR [r12+14728], 4294967295
__sbr_cell_37_778_end:
sbr_reset.L1d89:
__sbr_cell_37_779:
    mov WORD PTR [rbx+4], 65535
__sbr_cell_37_779_end:
__sbr_cell_37_780:
    mov DWORD PTR [rbx+0], 4294967295
__sbr_cell_37_780_end:
sbr_reset.L1d95:
__sbr_cell_37_781:
    add rsp, 1352
__sbr_cell_37_781_end:
__sbr_cell_37_782:
    pop rbx
__sbr_cell_37_782_end:
__sbr_cell_37_783:
    pop r12
__sbr_cell_37_783_end:
__sbr_cell_37_784:
    pop r13
__sbr_cell_37_784_end:
__sbr_cell_37_785:
    pop r14
__sbr_cell_37_785_end:
__sbr_cell_37_786:
    pop r15
__sbr_cell_37_786_end:
__sbr_cell_37_787:
    pop rbp
__sbr_cell_37_787_end:
sbr_reset.done:
__sbr_cell_37_788:
    ret
__sbr_cell_37_788_end:
sbr_reset.L1da7:
__sbr_cell_37_789:
    mov r13, QWORD PTR [rbp-72]
__sbr_cell_37_789_end:
__sbr_cell_37_790:
    mov DWORD PTR [r12+104], r13d
__sbr_cell_37_790_end:
__sbr_cell_37_791:
    movzx r14d, BYTE PTR [r12+30]
__sbr_cell_37_791_end:
__sbr_cell_37_792:
    movzx ecx, r14b
__sbr_cell_37_792_end:
__sbr_cell_37_793:
    cmp r13d, ecx
__sbr_cell_37_793_end:
__sbr_cell_37_794:
    jbe sbr_reset.L1e00
__sbr_cell_37_794_end:
__sbr_cell_37_795:
    lea rdi, [r12+311792]
__sbr_cell_37_795_end:
__sbr_cell_37_796:
    mov rdx, QWORD PTR [rbp-80]
__sbr_cell_37_796_end:
__sbr_cell_37_797:
    shl edx, 2
__sbr_cell_37_797_end:
__sbr_cell_37_798:
    or rdx, 2
__sbr_cell_37_798_end:
__sbr_cell_37_799:
    lea rsi, [rbp-368]
__sbr_cell_37_799_end:
sbr_reset.L1dd9:
__sbr_cell_37_800:
    call memcpy
__sbr_cell_37_800_end:
sbr_reset.L1dde:
__sbr_cell_37_801:
    jmp sbr_reset.L2012
__sbr_cell_37_801_end:
sbr_reset.L1de3:
__sbr_cell_37_802:
    sub r14d, r13d
__sbr_cell_37_802_end:
__sbr_cell_37_803:
    cdqe
__sbr_cell_37_803_end:
__sbr_cell_37_804:
    mov WORD PTR [rbp+rax*2-238], r14w
__sbr_cell_37_804_end:
__sbr_cell_37_805:
    movsx edi, WORD PTR [rbp-238]
__sbr_cell_37_805_end:
__sbr_cell_37_806:
    mov r13, rbx
__sbr_cell_37_806_end:
__sbr_cell_37_807:
    jmp sbr_reset.L2357
__sbr_cell_37_807_end:
sbr_reset.L1e00:
__sbr_cell_37_808:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_808_end:
__sbr_cell_37_809:
    jmp sbr_reset.L29ad
__sbr_cell_37_809_end:
sbr_reset.L1e09:
__sbr_cell_37_810:
    mov r8d, edx
__sbr_cell_37_810_end:
__sbr_cell_37_811:
    and r8d, 4294967264
__sbr_cell_37_811_end:
__sbr_cell_37_812:
    lea rdi, [r8+1]
__sbr_cell_37_812_end:
__sbr_cell_37_813:
    vmovd xmm0, eax
__sbr_cell_37_813_end:
__sbr_cell_37_814:
    vpshufb xmm0, xmm0, XMMWORD PTR [rip+LCPI5_4]
__sbr_cell_37_814_end:
__sbr_cell_37_815:
    xor r9d, r9d
__sbr_cell_37_815_end:
__sbr_cell_37_816:
    .nops 1
__sbr_cell_37_816_end:
sbr_reset.L1e30:
__sbr_cell_37_817:
    vmovdqu XMMWORD PTR [r12+r9*2+311794], xmm0
__sbr_cell_37_817_end:
__sbr_cell_37_818:
    vmovdqu XMMWORD PTR [r12+r9*2+311810], xmm0
__sbr_cell_37_818_end:
sbr_reset.L1e44:
__sbr_cell_37_819:
    vmovdqu XMMWORD PTR [r12+r9*2+311826], xmm0
__sbr_cell_37_819_end:
__sbr_cell_37_820:
    vmovdqu XMMWORD PTR [r12+r9*2+311842], xmm0
__sbr_cell_37_820_end:
__sbr_cell_37_821:
    add r9, 32
__sbr_cell_37_821_end:
__sbr_cell_37_822:
    cmp r8, r9
__sbr_cell_37_822_end:
__sbr_cell_37_823:
    jne sbr_reset.L1e30
__sbr_cell_37_823_end:
__sbr_cell_37_824:
    cmp r8d, edx
__sbr_cell_37_824_end:
__sbr_cell_37_825:
    je sbr_reset.L1ec1
__sbr_cell_37_825_end:
__sbr_cell_37_826:
    test dl, 24
__sbr_cell_37_826_end:
__sbr_cell_37_827:
    je sbr_reset.L1ea8
__sbr_cell_37_827_end:
sbr_reset.L1e6b:
__sbr_cell_37_828:
    mov r9d, edx
__sbr_cell_37_828_end:
__sbr_cell_37_829:
    and r9d, 4294967288
__sbr_cell_37_829_end:
__sbr_cell_37_830:
    lea rdi, [r9+1]
__sbr_cell_37_830_end:
__sbr_cell_37_831:
    vmovd xmm0, eax
__sbr_cell_37_831_end:
__sbr_cell_37_832:
    vpshufb xmm0, xmm0, XMMWORD PTR [rip+LCPI5_4]
__sbr_cell_37_832_end:
__sbr_cell_37_833:
    .nops 1
__sbr_cell_37_833_end:
sbr_reset.L1e90:
__sbr_cell_37_834:
    vmovdqu XMMWORD PTR [r12+r8*2+311794], xmm0
__sbr_cell_37_834_end:
__sbr_cell_37_835:
    add r8, 8
__sbr_cell_37_835_end:
__sbr_cell_37_836:
    cmp r9, r8
__sbr_cell_37_836_end:
__sbr_cell_37_837:
    jne sbr_reset.L1e90
__sbr_cell_37_837_end:
__sbr_cell_37_838:
    cmp r9d, edx
__sbr_cell_37_838_end:
__sbr_cell_37_839:
    je sbr_reset.L1ec1
__sbr_cell_37_839_end:
sbr_reset.L1ea8:
__sbr_cell_37_840:
    lea r8, [rdx+1]
__sbr_cell_37_840_end:
__sbr_cell_37_841:
    .nops 1
__sbr_cell_37_841_end:
sbr_reset.L1eb0:
__sbr_cell_37_842:
    mov WORD PTR [r12+rdi*2+311792], ax
__sbr_cell_37_842_end:
__sbr_cell_37_843:
    inc rdi
__sbr_cell_37_843_end:
__sbr_cell_37_844:
    cmp r8, rdi
__sbr_cell_37_844_end:
__sbr_cell_37_845:
    jne sbr_reset.L1eb0
__sbr_cell_37_845_end:
sbr_reset.L1ec1:
__sbr_cell_37_846:
    imul eax, ecx
__sbr_cell_37_846_end:
__sbr_cell_37_847:
    add eax, r13d
__sbr_cell_37_847_end:
__sbr_cell_37_848:
    sub esi, eax
__sbr_cell_37_848_end:
__sbr_cell_37_849:
    js sbr_reset.L1ed8
__sbr_cell_37_849_end:
__sbr_cell_37_850:
    je sbr_reset.L1f08
__sbr_cell_37_850_end:
__sbr_cell_37_851:
    inc WORD PTR [r12+rdx*2+311792]
__sbr_cell_37_851_end:
__sbr_cell_37_852:
    jmp sbr_reset.L1f08
__sbr_cell_37_852_end:
sbr_reset.L1ed8:
__sbr_cell_37_853:
    xor eax, eax
__sbr_cell_37_853_end:
__sbr_cell_37_854:
    cmp esi, 4294967295
__sbr_cell_37_854_end:
__sbr_cell_37_855:
    setne al
__sbr_cell_37_855_end:
__sbr_cell_37_856:
    neg eax
__sbr_cell_37_856_end:
__sbr_cell_37_857:
    vbroadcastss xmm0, DWORD PTR [rip+LCPI5_8]
__sbr_cell_37_857_end:
__sbr_cell_37_858:
    vpinsrw xmm0, xmm0, eax, 1
__sbr_cell_37_858_end:
__sbr_cell_37_859:
    vmovd xmm1, DWORD PTR [r12+311794]
__sbr_cell_37_859_end:
__sbr_cell_37_860:
    vpaddw xmm0, xmm1, xmm0
__sbr_cell_37_860_end:
__sbr_cell_37_861:
    vmovd DWORD PTR [r12+311794], xmm0
__sbr_cell_37_861_end:
sbr_reset.L1f08:
__sbr_cell_37_862:
    mov WORD PTR [r12+311792], r13w
__sbr_cell_37_862_end:
__sbr_cell_37_863:
    mov eax, 1
__sbr_cell_37_863_end:
__sbr_cell_37_864:
    cmp ecx, 8
__sbr_cell_37_864_end:
__sbr_cell_37_865:
    jb sbr_reset.L1fd5
__sbr_cell_37_865_end:
__sbr_cell_37_866:
    mov ecx, edx
__sbr_cell_37_866_end:
__sbr_cell_37_867:
    and ecx, 4294967288
__sbr_cell_37_867_end:
__sbr_cell_37_868:
    xor eax, eax
__sbr_cell_37_868_end:
__sbr_cell_37_869:
    .nops 1
__sbr_cell_37_869_end:
sbr_reset.L1f30:
__sbr_cell_37_870:
    add r13w, WORD PTR [r12+rax*2+311794]
__sbr_cell_37_870_end:
__sbr_cell_37_871:
    mov WORD PTR [r12+rax*2+311794], r13w
__sbr_cell_37_871_end:
__sbr_cell_37_872:
    add r13w, WORD PTR [r12+rax*2+311796]
__sbr_cell_37_872_end:
__sbr_cell_37_873:
    mov WORD PTR [r12+rax*2+311796], r13w
__sbr_cell_37_873_end:
__sbr_cell_37_874:
    add r13w, WORD PTR [r12+rax*2+311798]
__sbr_cell_37_874_end:
sbr_reset.L1f5d:
__sbr_cell_37_875:
    mov WORD PTR [r12+rax*2+311798], r13w
__sbr_cell_37_875_end:
__sbr_cell_37_876:
    add r13w, WORD PTR [r12+rax*2+311800]
__sbr_cell_37_876_end:
__sbr_cell_37_877:
    mov WORD PTR [r12+rax*2+311800], r13w
__sbr_cell_37_877_end:
__sbr_cell_37_878:
    add r13w, WORD PTR [r12+rax*2+311802]
__sbr_cell_37_878_end:
sbr_reset.L1f81:
__sbr_cell_37_879:
    mov WORD PTR [r12+rax*2+311802], r13w
__sbr_cell_37_879_end:
__sbr_cell_37_880:
    add r13w, WORD PTR [r12+rax*2+311804]
__sbr_cell_37_880_end:
__sbr_cell_37_881:
    mov WORD PTR [r12+rax*2+311804], r13w
__sbr_cell_37_881_end:
__sbr_cell_37_882:
    add r13w, WORD PTR [r12+rax*2+311806]
__sbr_cell_37_882_end:
sbr_reset.L1fa5:
__sbr_cell_37_883:
    mov WORD PTR [r12+rax*2+311806], r13w
__sbr_cell_37_883_end:
__sbr_cell_37_884:
    add r13w, WORD PTR [r12+rax*2+311808]
__sbr_cell_37_884_end:
__sbr_cell_37_885:
    mov WORD PTR [r12+rax*2+311808], r13w
__sbr_cell_37_885_end:
__sbr_cell_37_886:
    add rax, 8
__sbr_cell_37_886_end:
__sbr_cell_37_887:
    cmp rcx, rax
__sbr_cell_37_887_end:
__sbr_cell_37_888:
    jne sbr_reset.L1f30
__sbr_cell_37_888_end:
__sbr_cell_37_889:
    test dl, 6
__sbr_cell_37_889_end:
__sbr_cell_37_890:
    je sbr_reset.L2003
__sbr_cell_37_890_end:
__sbr_cell_37_891:
    inc rax
__sbr_cell_37_891_end:
sbr_reset.L1fd5:
__sbr_cell_37_892:
    lea rax, [r12+rax*2+0]
__sbr_cell_37_892_end:
__sbr_cell_37_893:
    add rax, 311792
__sbr_cell_37_893_end:
__sbr_cell_37_894:
    lea ecx, [rdx+rdx*1+0]
__sbr_cell_37_894_end:
__sbr_cell_37_895:
    and ecx, 12
__sbr_cell_37_895_end:
__sbr_cell_37_896:
    xor edx, edx
__sbr_cell_37_896_end:
__sbr_cell_37_897:
    .nops 1
__sbr_cell_37_897_end:
sbr_reset.L1ff0:
__sbr_cell_37_898:
    add r13w, WORD PTR [rax+rdx*1+0]
__sbr_cell_37_898_end:
__sbr_cell_37_899:
    mov WORD PTR [rax+rdx*1+0], r13w
__sbr_cell_37_899_end:
__sbr_cell_37_900:
    add rdx, 2
__sbr_cell_37_900_end:
__sbr_cell_37_901:
    cmp rcx, rdx
__sbr_cell_37_901_end:
__sbr_cell_37_902:
    jne sbr_reset.L1ff0
__sbr_cell_37_902_end:
sbr_reset.L2003:
__sbr_cell_37_903:
    mov QWORD PTR [rbp-64], r15
__sbr_cell_37_903_end:
__sbr_cell_37_904:
    mov r13d, DWORD PTR [r12+104]
__sbr_cell_37_904_end:
__sbr_cell_37_905:
    movzx r14d, BYTE PTR [r12+30]
__sbr_cell_37_905_end:
sbr_reset.L2012:
__sbr_cell_37_906:
    movzx eax, r14b
__sbr_cell_37_906_end:
__sbr_cell_37_907:
    mov QWORD PTR [rbp-56], r13
__sbr_cell_37_907_end:
__sbr_cell_37_908:
    sub r13d, eax
__sbr_cell_37_908_end:
__sbr_cell_37_909:
    mov DWORD PTR [r12+311780], r13d
__sbr_cell_37_909_end:
__sbr_cell_37_910:
    mov rbx, r12
__sbr_cell_37_910_end:
__sbr_cell_37_911:
    lea r12d, [r13+1]
__sbr_cell_37_911_end:
__sbr_cell_37_912:
    mov r15d, r12d
__sbr_cell_37_912_end:
__sbr_cell_37_913:
    shr r15d, 1
__sbr_cell_37_913_end:
sbr_reset.L2032:
__sbr_cell_37_914:
    mov DWORD PTR [rbx+311776], r15d
__sbr_cell_37_914_end:
__sbr_cell_37_915:
    cmp al, 50
__sbr_cell_37_915_end:
__sbr_cell_37_916:
    jae sbr_reset.L32c8
__sbr_cell_37_916_end:
__sbr_cell_37_917:
    lea rdi, [rbx+311940]
__sbr_cell_37_917_end:
__sbr_cell_37_918:
    lea rsi, [rbx+rax*2+0]
__sbr_cell_37_918_end:
__sbr_cell_37_919:
    add rsi, 311792
__sbr_cell_37_919_end:
__sbr_cell_37_920:
    mov edx, r12d
__sbr_cell_37_920_end:
__sbr_cell_37_921:
    add rdx, rdx
__sbr_cell_37_921_end:
sbr_reset.L2059:
__sbr_cell_37_922:
    call memcpy
__sbr_cell_37_922_end:
sbr_reset.L205e:
__sbr_cell_37_923:
    cmp r13d, 49
__sbr_cell_37_923_end:
__sbr_cell_37_924:
    jae sbr_reset.L32cd
__sbr_cell_37_924_end:
__sbr_cell_37_925:
    mov eax, r13d
__sbr_cell_37_925_end:
__sbr_cell_37_926:
    movzx ecx, WORD PTR [rbx+rax*2+311940]
__sbr_cell_37_926_end:
__sbr_cell_37_927:
    movzx r14d, WORD PTR [rbx+311940]
__sbr_cell_37_927_end:
__sbr_cell_37_928:
    movzx r10d, r14w
__sbr_cell_37_928_end:
__sbr_cell_37_929:
    mov eax, ecx
__sbr_cell_37_929_end:
__sbr_cell_37_930:
    sub eax, r10d
__sbr_cell_37_930_end:
__sbr_cell_37_931:
    mov DWORD PTR [rbx+96], eax
__sbr_cell_37_931_end:
__sbr_cell_37_932:
    mov QWORD PTR [rbp-48], rbx
__sbr_cell_37_932_end:
sbr_reset.L208b:
__sbr_cell_37_933:
    mov DWORD PTR [rbx+88], r10d
__sbr_cell_37_933_end:
__sbr_cell_37_934:
    cmp ecx, 65
__sbr_cell_37_934_end:
__sbr_cell_37_935:
    jb sbr_reset.L20aa
__sbr_cell_37_935_end:
__sbr_cell_37_936:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_936_end:
__sbr_cell_37_937:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_937_end:
__sbr_cell_37_938:
    lea rdx, [rip+L_str_16]
__sbr_cell_37_938_end:
__sbr_cell_37_939:
    mov esi, 16
__sbr_cell_37_939_end:
__sbr_cell_37_940:
    jmp sbr_reset.L20c8
__sbr_cell_37_940_end:
sbr_reset.L20aa:
__sbr_cell_37_941:
    cmp r14w, 33
__sbr_cell_37_941_end:
__sbr_cell_37_942:
    jb sbr_reset.L20d8
__sbr_cell_37_942_end:
__sbr_cell_37_943:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_943_end:
__sbr_cell_37_944:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_944_end:
__sbr_cell_37_945:
    lea rdx, [rip+L_str_17]
__sbr_cell_37_945_end:
__sbr_cell_37_946:
    mov esi, 16
__sbr_cell_37_946_end:
__sbr_cell_37_947:
    mov ecx, r10d
__sbr_cell_37_947_end:
sbr_reset.L20c8:
__sbr_cell_37_948:
    xor eax, eax
__sbr_cell_37_948_end:
__sbr_cell_37_949:
    call av_log
__sbr_cell_37_949_end:
sbr_reset.L20cf:
__sbr_cell_37_950:
    mov r12, QWORD PTR [rbp-48]
__sbr_cell_37_950_end:
__sbr_cell_37_951:
    jmp sbr_reset.L1d31
__sbr_cell_37_951_end:
sbr_reset.L20d8:
__sbr_cell_37_952:
    mov rax, QWORD PTR [rbp-48]
__sbr_cell_37_952_end:
__sbr_cell_37_953:
    mov WORD PTR [rax+311890], r14w
__sbr_cell_37_953_end:
__sbr_cell_37_954:
    test r15d, r15d
__sbr_cell_37_954_end:
__sbr_cell_37_955:
    je sbr_reset.L2b30
__sbr_cell_37_955_end:
__sbr_cell_37_956:
    and r13d, 1
__sbr_cell_37_956_end:
__sbr_cell_37_957:
    mov eax, 1
__sbr_cell_37_957_end:
__sbr_cell_37_958:
    cmp r12d, 10
__sbr_cell_37_958_end:
__sbr_cell_37_959:
    jb sbr_reset.L2aef
__sbr_cell_37_959_end:
__sbr_cell_37_960:
    cmp r12d, 34
__sbr_cell_37_960_end:
__sbr_cell_37_961:
    jae sbr_reset.L29f4
__sbr_cell_37_961_end:
__sbr_cell_37_962:
    xor r9d, r9d
__sbr_cell_37_962_end:
__sbr_cell_37_963:
    jmp sbr_reset.L2a85
__sbr_cell_37_963_end:
sbr_reset.L2112:
__sbr_cell_37_964:
    mov rsi, rax
__sbr_cell_37_964_end:
__sbr_cell_37_965:
    and esi, 2147483640
__sbr_cell_37_965_end:
__sbr_cell_37_966:
    xor edx, edx
__sbr_cell_37_966_end:
__sbr_cell_37_967:
    vmovaps xmm1, XMMWORD PTR [rbp-128]
__sbr_cell_37_967_end:
__sbr_cell_37_968:
    .nops 1
__sbr_cell_37_968_end:
sbr_reset.L2130:
__sbr_cell_37_969:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_969_end:
__sbr_cell_37_970:
    vcvtss2si rdi, xmm1
__sbr_cell_37_970_end:
__sbr_cell_37_971:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_971_end:
__sbr_cell_37_972:
    vcvtss2si r8, xmm1
__sbr_cell_37_972_end:
__sbr_cell_37_973:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_973_end:
__sbr_cell_37_974:
    vcvtss2si r9, xmm1
__sbr_cell_37_974_end:
__sbr_cell_37_975:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_975_end:
__sbr_cell_37_976:
    vcvtss2si r10, xmm1
__sbr_cell_37_976_end:
__sbr_cell_37_977:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_977_end:
__sbr_cell_37_978:
    vcvtss2si r11, xmm1
__sbr_cell_37_978_end:
__sbr_cell_37_979:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_979_end:
__sbr_cell_37_980:
    vcvtss2si rbx, xmm1
__sbr_cell_37_980_end:
sbr_reset.L2166:
__sbr_cell_37_981:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_981_end:
__sbr_cell_37_982:
    vcvtss2si r12, xmm1
__sbr_cell_37_982_end:
__sbr_cell_37_983:
    mov eax, r12d
__sbr_cell_37_983_end:
__sbr_cell_37_984:
    sub eax, ebx
__sbr_cell_37_984_end:
__sbr_cell_37_985:
    sub ebx, r11d
__sbr_cell_37_985_end:
__sbr_cell_37_986:
    sub r11d, r10d
__sbr_cell_37_986_end:
__sbr_cell_37_987:
    sub r10d, r9d
__sbr_cell_37_987_end:
__sbr_cell_37_988:
    sub r9d, r8d
__sbr_cell_37_988_end:
__sbr_cell_37_989:
    sub r8d, edi
__sbr_cell_37_989_end:
__sbr_cell_37_990:
    sub edi, r13d
__sbr_cell_37_990_end:
__sbr_cell_37_991:
    mov WORD PTR [rbp+rdx*2-238], di
__sbr_cell_37_991_end:
__sbr_cell_37_992:
    mov WORD PTR [rbp+rdx*2-236], r8w
__sbr_cell_37_992_end:
sbr_reset.L2197:
__sbr_cell_37_993:
    mov WORD PTR [rbp+rdx*2-234], r9w
__sbr_cell_37_993_end:
__sbr_cell_37_994:
    mov WORD PTR [rbp+rdx*2-232], r10w
__sbr_cell_37_994_end:
sbr_reset.L21a9:
__sbr_cell_37_995:
    mov WORD PTR [rbp+rdx*2-230], r11w
__sbr_cell_37_995_end:
__sbr_cell_37_996:
    mov WORD PTR [rbp+rdx*2-228], bx
__sbr_cell_37_996_end:
sbr_reset.L21ba:
__sbr_cell_37_997:
    mov WORD PTR [rbp+rdx*2-226], ax
__sbr_cell_37_997_end:
__sbr_cell_37_998:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_998_end:
__sbr_cell_37_999:
    vcvtss2si r13, xmm1
__sbr_cell_37_999_end:
__sbr_cell_37_1000:
    mov eax, r13d
__sbr_cell_37_1000_end:
__sbr_cell_37_1001:
    sub eax, r12d
__sbr_cell_37_1001_end:
__sbr_cell_37_1002:
    mov WORD PTR [rbp+rdx*2-224], ax
__sbr_cell_37_1002_end:
__sbr_cell_37_1003:
    add rdx, 8
__sbr_cell_37_1003_end:
__sbr_cell_37_1004:
    cmp rsi, rdx
__sbr_cell_37_1004_end:
__sbr_cell_37_1005:
    jne sbr_reset.L2130
__sbr_cell_37_1005_end:
sbr_reset.L21e6:
__sbr_cell_37_1006:
    lea rdx, [rdx*2-238]
__sbr_cell_37_1006_end:
__sbr_cell_37_1007:
    add rdx, rbp
__sbr_cell_37_1007_end:
__sbr_cell_37_1008:
    xor esi, esi
__sbr_cell_37_1008_end:
__sbr_cell_37_1009:
    .nops 1
__sbr_cell_37_1009_end:
sbr_reset.L2200:
__sbr_cell_37_1010:
    mov eax, r13d
__sbr_cell_37_1010_end:
__sbr_cell_37_1011:
    vmulss xmm1, xmm0, xmm1
__sbr_cell_37_1011_end:
__sbr_cell_37_1012:
    vcvtss2si r13, xmm1
__sbr_cell_37_1012_end:
__sbr_cell_37_1013:
    mov edi, r13d
__sbr_cell_37_1013_end:
__sbr_cell_37_1014:
    sub edi, eax
__sbr_cell_37_1014_end:
__sbr_cell_37_1015:
    mov WORD PTR [rdx+rsi*2+0], di
__sbr_cell_37_1015_end:
__sbr_cell_37_1016:
    inc rsi
__sbr_cell_37_1016_end:
__sbr_cell_37_1017:
    cmp rcx, rsi
__sbr_cell_37_1017_end:
__sbr_cell_37_1018:
    jne sbr_reset.L2200
__sbr_cell_37_1018_end:
__sbr_cell_37_1019:
    sub r14d, r13d
__sbr_cell_37_1019_end:
__sbr_cell_37_1020:
    mov rax, QWORD PTR [rbp-256]
__sbr_cell_37_1020_end:
__sbr_cell_37_1021:
    mov WORD PTR [rbp+rax*2-238], r14w
__sbr_cell_37_1021_end:
sbr_reset.L2230:
__sbr_cell_37_1022:
    movsx edi, WORD PTR [rbp-238]
__sbr_cell_37_1022_end:
__sbr_cell_37_1023:
    mov r13, QWORD PTR [rbp-56]
__sbr_cell_37_1023_end:
__sbr_cell_37_1024:
    mov eax, r13d
__sbr_cell_37_1024_end:
__sbr_cell_37_1025:
    mov ecx, 1
__sbr_cell_37_1025_end:
__sbr_cell_37_1026:
    cmp r13d, 5
__sbr_cell_37_1026_end:
__sbr_cell_37_1027:
    jae sbr_reset.L2252
__sbr_cell_37_1027_end:
__sbr_cell_37_1028:
    mov r12, QWORD PTR [rbp-48]
__sbr_cell_37_1028_end:
__sbr_cell_37_1029:
    jmp sbr_reset.L2340
__sbr_cell_37_1029_end:
sbr_reset.L2252:
__sbr_cell_37_1030:
    lea rdx, [rax-1]
__sbr_cell_37_1030_end:
__sbr_cell_37_1031:
    cmp r13d, 17
__sbr_cell_37_1031_end:
__sbr_cell_37_1032:
    mov r12, QWORD PTR [rbp-48]
__sbr_cell_37_1032_end:
__sbr_cell_37_1033:
    jae sbr_reset.L2267
__sbr_cell_37_1033_end:
__sbr_cell_37_1034:
    xor esi, esi
__sbr_cell_37_1034_end:
__sbr_cell_37_1035:
    jmp sbr_reset.L22fa
__sbr_cell_37_1035_end:
sbr_reset.L2267:
__sbr_cell_37_1036:
    mov rsi, rdx
__sbr_cell_37_1036_end:
__sbr_cell_37_1037:
    and rsi, -16
__sbr_cell_37_1037_end:
__sbr_cell_37_1038:
    lea rcx, [rsi+1]
__sbr_cell_37_1038_end:
__sbr_cell_37_1039:
    vmovd xmm0, edi
__sbr_cell_37_1039_end:
__sbr_cell_37_1040:
    vpshufd xmm0, xmm0, 0
__sbr_cell_37_1040_end:
__sbr_cell_37_1041:
    xor edi, edi
__sbr_cell_37_1041_end:
__sbr_cell_37_1042:
    vmovdqa xmm1, xmm0
__sbr_cell_37_1042_end:
__sbr_cell_37_1043:
    vmovdqa xmm2, xmm0
__sbr_cell_37_1043_end:
__sbr_cell_37_1044:
    vmovdqa xmm3, xmm0
__sbr_cell_37_1044_end:
sbr_reset.L2289:
__sbr_cell_37_1045:
    vpmovsxwd xmm4, QWORD PTR [rbp+rdi*2-236]
__sbr_cell_37_1045_end:
__sbr_cell_37_1046:
    vpminsd xmm0, xmm0, xmm4
__sbr_cell_37_1046_end:
__sbr_cell_37_1047:
    vpmovsxwd xmm4, QWORD PTR [rbp+rdi*2-228]
__sbr_cell_37_1047_end:
__sbr_cell_37_1048:
    vpminsd xmm1, xmm1, xmm4
__sbr_cell_37_1048_end:
__sbr_cell_37_1049:
    vpmovsxwd xmm4, QWORD PTR [rbp+rdi*2-220]
__sbr_cell_37_1049_end:
__sbr_cell_37_1050:
    vpmovsxwd xmm5, QWORD PTR [rbp+rdi*2-212]
__sbr_cell_37_1050_end:
__sbr_cell_37_1051:
    vpminsd xmm2, xmm2, xmm4
__sbr_cell_37_1051_end:
__sbr_cell_37_1052:
    vpminsd xmm3, xmm3, xmm5
__sbr_cell_37_1052_end:
__sbr_cell_37_1053:
    add rdi, 16
__sbr_cell_37_1053_end:
__sbr_cell_37_1054:
    cmp rsi, rdi
__sbr_cell_37_1054_end:
__sbr_cell_37_1055:
    jne sbr_reset.L2289
__sbr_cell_37_1055_end:
__sbr_cell_37_1056:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1056_end:
sbr_reset.L22d3:
__sbr_cell_37_1057:
    vpminsd xmm1, xmm2, xmm3
__sbr_cell_37_1057_end:
__sbr_cell_37_1058:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1058_end:
__sbr_cell_37_1059:
    vpshufd xmm1, xmm0, 238
__sbr_cell_37_1059_end:
__sbr_cell_37_1060:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1060_end:
__sbr_cell_37_1061:
    vpshufd xmm1, xmm0, 85
__sbr_cell_37_1061_end:
__sbr_cell_37_1062:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1062_end:
__sbr_cell_37_1063:
    vmovd edi, xmm0
__sbr_cell_37_1063_end:
__sbr_cell_37_1064:
    test dl, 12
__sbr_cell_37_1064_end:
__sbr_cell_37_1065:
    je sbr_reset.L2340
__sbr_cell_37_1065_end:
sbr_reset.L22fa:
__sbr_cell_37_1066:
    and rdx, -4
__sbr_cell_37_1066_end:
__sbr_cell_37_1067:
    lea rcx, [rdx+1]
__sbr_cell_37_1067_end:
__sbr_cell_37_1068:
    vmovd xmm0, edi
__sbr_cell_37_1068_end:
__sbr_cell_37_1069:
    vpshufd xmm0, xmm0, 0
__sbr_cell_37_1069_end:
__sbr_cell_37_1070:
    .nops 1
__sbr_cell_37_1070_end:
sbr_reset.L2310:
__sbr_cell_37_1071:
    vpmovsxwd xmm1, QWORD PTR [rbp+rsi*2-236]
__sbr_cell_37_1071_end:
__sbr_cell_37_1072:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1072_end:
__sbr_cell_37_1073:
    add rsi, 4
__sbr_cell_37_1073_end:
__sbr_cell_37_1074:
    cmp rdx, rsi
__sbr_cell_37_1074_end:
__sbr_cell_37_1075:
    jne sbr_reset.L2310
__sbr_cell_37_1075_end:
__sbr_cell_37_1076:
    vpshufd xmm1, xmm0, 238
__sbr_cell_37_1076_end:
__sbr_cell_37_1077:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1077_end:
__sbr_cell_37_1078:
    vpshufd xmm1, xmm0, 85
__sbr_cell_37_1078_end:
__sbr_cell_37_1079:
    vpminsd xmm0, xmm0, xmm1
__sbr_cell_37_1079_end:
__sbr_cell_37_1080:
    vmovd edi, xmm0
__sbr_cell_37_1080_end:
sbr_reset.L2340:
__sbr_cell_37_1081:
    mov edx, edi
__sbr_cell_37_1081_end:
__sbr_cell_37_1082:
    movsx edi, WORD PTR [rbp+rcx*2-238]
__sbr_cell_37_1082_end:
__sbr_cell_37_1083:
    cmp edx, edi
__sbr_cell_37_1083_end:
__sbr_cell_37_1084:
    cmovl edi, edx
__sbr_cell_37_1084_end:
__sbr_cell_37_1085:
    inc rcx
__sbr_cell_37_1085_end:
__sbr_cell_37_1086:
    cmp rax, rcx
__sbr_cell_37_1086_end:
__sbr_cell_37_1087:
    jne sbr_reset.L2340
__sbr_cell_37_1087_end:
sbr_reset.L2357:
__sbr_cell_37_1088:
    lea rax, [rbp-238]
__sbr_cell_37_1088_end:
__sbr_cell_37_1089:
    cmp edi, DWORD PTR [rbp-80]
__sbr_cell_37_1089_end:
__sbr_cell_37_1090:
    jge sbr_reset.L25ca
__sbr_cell_37_1090_end:
__sbr_cell_37_1091:
    mov QWORD PTR [rbp-1392], rax
__sbr_cell_37_1091_end:
__sbr_cell_37_1092:
    movsxd rcx, r13d
__sbr_cell_37_1092_end:
__sbr_cell_37_1093:
    mov QWORD PTR [rbp-48], rcx
__sbr_cell_37_1093_end:
__sbr_cell_37_1094:
    lea rax, [rax+rcx*2+0]
__sbr_cell_37_1094_end:
__sbr_cell_37_1095:
    add rax, -2
__sbr_cell_37_1095_end:
sbr_reset.L237d:
__sbr_cell_37_1096:
    mov QWORD PTR [rbp-1384], rax
__sbr_cell_37_1096_end:
__sbr_cell_37_1097:
    mov eax, 1
__sbr_cell_37_1097_end:
__sbr_cell_37_1098:
    jmp sbr_reset.L2398
__sbr_cell_37_1098_end:
__sbr_cell_37_1099:
    .nops 1
__sbr_cell_37_1099_end:
sbr_reset.L2390:
__sbr_cell_37_1100:
    test eax, eax
__sbr_cell_37_1100_end:
__sbr_cell_37_1101:
    je sbr_reset.L25cf
__sbr_cell_37_1101_end:
sbr_reset.L2398:
__sbr_cell_37_1102:
    cmp eax, 65
__sbr_cell_37_1102_end:
__sbr_cell_37_1103:
    jae sbr_reset.L3289
__sbr_cell_37_1103_end:
__sbr_cell_37_1104:
    dec eax
__sbr_cell_37_1104_end:
__sbr_cell_37_1105:
    mov rcx, rax
__sbr_cell_37_1105_end:
__sbr_cell_37_1106:
    shl rcx, 4
__sbr_cell_37_1106_end:
__sbr_cell_37_1107:
    mov rdx, QWORD PTR [rbp+rcx*1-1392]
__sbr_cell_37_1107_end:
__sbr_cell_37_1108:
    mov rcx, QWORD PTR [rbp+rcx*1-1384]
__sbr_cell_37_1108_end:
__sbr_cell_37_1109:
    .nops 1
__sbr_cell_37_1109_end:
sbr_reset.L23c0:
__sbr_cell_37_1110:
    cmp rdx, rcx
__sbr_cell_37_1110_end:
__sbr_cell_37_1111:
    jae sbr_reset.L2390
__sbr_cell_37_1111_end:
__sbr_cell_37_1112:
    lea rdi, [rcx-2]
__sbr_cell_37_1112_end:
__sbr_cell_37_1113:
    cmp rdx, rdi
__sbr_cell_37_1113_end:
__sbr_cell_37_1114:
    jae sbr_reset.L25b0
__sbr_cell_37_1114_end:
__sbr_cell_37_1115:
    mov r8, rcx
__sbr_cell_37_1115_end:
__sbr_cell_37_1116:
    sub r8, rdx
__sbr_cell_37_1116_end:
__sbr_cell_37_1117:
    sar r8, 2
__sbr_cell_37_1117_end:
__sbr_cell_37_1118:
    lea rsi, [rdx+r8*2+0]
__sbr_cell_37_1118_end:
__sbr_cell_37_1119:
    movzx r9d, WORD PTR [rdx+0]
__sbr_cell_37_1119_end:
__sbr_cell_37_1120:
    movzx r11d, WORD PTR [rcx+0]
__sbr_cell_37_1120_end:
__sbr_cell_37_1121:
    movzx r8d, WORD PTR [rdx+r8*2+0]
__sbr_cell_37_1121_end:
sbr_reset.L23ed:
__sbr_cell_37_1122:
    cmp r9w, r11w
__sbr_cell_37_1122_end:
__sbr_cell_37_1123:
    jle sbr_reset.L2410
__sbr_cell_37_1123_end:
__sbr_cell_37_1124:
    cmp r11w, r8w
__sbr_cell_37_1124_end:
__sbr_cell_37_1125:
    jg sbr_reset.L241c
__sbr_cell_37_1125_end:
__sbr_cell_37_1126:
    mov WORD PTR [rcx+0], r9w
__sbr_cell_37_1126_end:
__sbr_cell_37_1127:
    mov r8d, r11d
__sbr_cell_37_1127_end:
__sbr_cell_37_1128:
    jmp sbr_reset.L2420
__sbr_cell_37_1128_end:
__sbr_cell_37_1129:
    .nops 1
__sbr_cell_37_1129_end:
sbr_reset.L2410:
__sbr_cell_37_1130:
    mov r10d, 1
__sbr_cell_37_1130_end:
__sbr_cell_37_1131:
    cmp r9w, r8w
__sbr_cell_37_1131_end:
__sbr_cell_37_1132:
    jle sbr_reset.L242f
__sbr_cell_37_1132_end:
sbr_reset.L241c:
__sbr_cell_37_1133:
    mov WORD PTR [rsi+0], r9w
__sbr_cell_37_1133_end:
sbr_reset.L2420:
__sbr_cell_37_1134:
    mov WORD PTR [rdx+0], r8w
__sbr_cell_37_1134_end:
__sbr_cell_37_1135:
    movzx r8d, WORD PTR [rsi+0]
__sbr_cell_37_1135_end:
__sbr_cell_37_1136:
    movzx r11d, WORD PTR [rcx+0]
__sbr_cell_37_1136_end:
__sbr_cell_37_1137:
    xor r10d, r10d
__sbr_cell_37_1137_end:
sbr_reset.L242f:
__sbr_cell_37_1138:
    cmp r8w, r11w
__sbr_cell_37_1138_end:
__sbr_cell_37_1139:
    jle sbr_reset.L2450
__sbr_cell_37_1139_end:
__sbr_cell_37_1140:
    mov WORD PTR [rcx+0], r8w
__sbr_cell_37_1140_end:
__sbr_cell_37_1141:
    mov WORD PTR [rsi+0], r11w
__sbr_cell_37_1141_end:
__sbr_cell_37_1142:
    xor r10d, r10d
__sbr_cell_37_1142_end:
__sbr_cell_37_1143:
    lea r8, [rcx-4]
__sbr_cell_37_1143_end:
__sbr_cell_37_1144:
    cmp rdx, r8
__sbr_cell_37_1144_end:
__sbr_cell_37_1145:
    jne sbr_reset.L2460
__sbr_cell_37_1145_end:
__sbr_cell_37_1146:
    jmp sbr_reset.L2390
__sbr_cell_37_1146_end:
__sbr_cell_37_1147:
    .nops 1
__sbr_cell_37_1147_end:
sbr_reset.L2450:
__sbr_cell_37_1148:
    mov r11d, r8d
__sbr_cell_37_1148_end:
__sbr_cell_37_1149:
    lea r8, [rcx-4]
__sbr_cell_37_1149_end:
__sbr_cell_37_1150:
    cmp rdx, r8
__sbr_cell_37_1150_end:
__sbr_cell_37_1151:
    je sbr_reset.L2390
__sbr_cell_37_1151_end:
sbr_reset.L2460:
__sbr_cell_37_1152:
    lea r9, [rdx+2]
__sbr_cell_37_1152_end:
__sbr_cell_37_1153:
    movzx ebx, WORD PTR [rdi+0]
__sbr_cell_37_1153_end:
__sbr_cell_37_1154:
    mov WORD PTR [rsi+0], bx
__sbr_cell_37_1154_end:
__sbr_cell_37_1155:
    mov WORD PTR [rdi+0], r11w
__sbr_cell_37_1155_end:
__sbr_cell_37_1156:
    cmp r9, r8
__sbr_cell_37_1156_end:
__sbr_cell_37_1157:
    jbe sbr_reset.L2499
__sbr_cell_37_1157_end:
__sbr_cell_37_1158:
    jmp sbr_reset.L24e4
__sbr_cell_37_1158_end:
__sbr_cell_37_1159:
    .nops 1
__sbr_cell_37_1159_end:
sbr_reset.L2480:
__sbr_cell_37_1160:
    movzx r11d, WORD PTR [r9+0]
__sbr_cell_37_1160_end:
__sbr_cell_37_1161:
    mov WORD PTR [r8+0], r11w
__sbr_cell_37_1161_end:
__sbr_cell_37_1162:
    mov WORD PTR [r9+0], r14w
__sbr_cell_37_1162_end:
__sbr_cell_37_1163:
    add r9, 2
__sbr_cell_37_1163_end:
__sbr_cell_37_1164:
    add r8, -2
__sbr_cell_37_1164_end:
sbr_reset.L2494:
__sbr_cell_37_1165:
    cmp r9, r8
__sbr_cell_37_1165_end:
__sbr_cell_37_1166:
    ja sbr_reset.L24e0
__sbr_cell_37_1166_end:
sbr_reset.L2499:
__sbr_cell_37_1167:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_1167_end:
__sbr_cell_37_1168:
    .nops 1
__sbr_cell_37_1168_end:
sbr_reset.L24a0:
__sbr_cell_37_1169:
    cmp WORD PTR [r9+0], r11w
__sbr_cell_37_1169_end:
__sbr_cell_37_1170:
    jge sbr_reset.L24c4
__sbr_cell_37_1170_end:
__sbr_cell_37_1171:
    add r9, 2
__sbr_cell_37_1171_end:
__sbr_cell_37_1172:
    cmp r9, r8
__sbr_cell_37_1172_end:
__sbr_cell_37_1173:
    jbe sbr_reset.L24a0
__sbr_cell_37_1173_end:
__sbr_cell_37_1174:
    jmp sbr_reset.L24c4
__sbr_cell_37_1174_end:
__sbr_cell_37_1175:
    .nops 1
__sbr_cell_37_1175_end:
sbr_reset.L24c0:
__sbr_cell_37_1176:
    add r8, -2
__sbr_cell_37_1176_end:
sbr_reset.L24c4:
__sbr_cell_37_1177:
    cmp r9, r8
__sbr_cell_37_1177_end:
__sbr_cell_37_1178:
    ja sbr_reset.L2494
__sbr_cell_37_1178_end:
__sbr_cell_37_1179:
    movzx r14d, WORD PTR [r8+0]
__sbr_cell_37_1179_end:
__sbr_cell_37_1180:
    cmp r14w, r11w
__sbr_cell_37_1180_end:
__sbr_cell_37_1181:
    jg sbr_reset.L24c0
__sbr_cell_37_1181_end:
__sbr_cell_37_1182:
    jmp sbr_reset.L2480
__sbr_cell_37_1182_end:
__sbr_cell_37_1183:
    .nops 1
__sbr_cell_37_1183_end:
sbr_reset.L24e0:
__sbr_cell_37_1184:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_1184_end:
sbr_reset.L24e4:
__sbr_cell_37_1185:
    movzx ebx, WORD PTR [r9+0]
__sbr_cell_37_1185_end:
__sbr_cell_37_1186:
    mov WORD PTR [r9+0], r11w
__sbr_cell_37_1186_end:
__sbr_cell_37_1187:
    mov WORD PTR [rdi+0], bx
__sbr_cell_37_1187_end:
__sbr_cell_37_1188:
    test r10d, r10d
__sbr_cell_37_1188_end:
__sbr_cell_37_1189:
    je sbr_reset.L2530
__sbr_cell_37_1189_end:
__sbr_cell_37_1190:
    cmp rsi, r9
__sbr_cell_37_1190_end:
__sbr_cell_37_1191:
    je sbr_reset.L2502
__sbr_cell_37_1191_end:
__sbr_cell_37_1192:
    lea rdi, [r9-2]
__sbr_cell_37_1192_end:
__sbr_cell_37_1193:
    cmp rsi, rdi
__sbr_cell_37_1193_end:
__sbr_cell_37_1194:
    jne sbr_reset.L2530
__sbr_cell_37_1194_end:
sbr_reset.L2502:
__sbr_cell_37_1195:
    mov rdi, rdx
__sbr_cell_37_1195_end:
__sbr_cell_37_1196:
    .nops 1
__sbr_cell_37_1196_end:
sbr_reset.L2510:
__sbr_cell_37_1197:
    mov rsi, rdi
__sbr_cell_37_1197_end:
__sbr_cell_37_1198:
    cmp rdi, rcx
__sbr_cell_37_1198_end:
__sbr_cell_37_1199:
    jae sbr_reset.L2527
__sbr_cell_37_1199_end:
__sbr_cell_37_1200:
    lea rdi, [rsi+2]
__sbr_cell_37_1200_end:
__sbr_cell_37_1201:
    movzx r10d, WORD PTR [rsi+0]
__sbr_cell_37_1201_end:
__sbr_cell_37_1202:
    cmp r10w, WORD PTR [rsi+2]
__sbr_cell_37_1202_end:
__sbr_cell_37_1203:
    jle sbr_reset.L2510
__sbr_cell_37_1203_end:
sbr_reset.L2527:
__sbr_cell_37_1204:
    cmp rsi, rcx
__sbr_cell_37_1204_end:
__sbr_cell_37_1205:
    je sbr_reset.L2390
__sbr_cell_37_1205_end:
sbr_reset.L2530:
__sbr_cell_37_1206:
    mov rsi, rcx
__sbr_cell_37_1206_end:
__sbr_cell_37_1207:
    sub rsi, r9
__sbr_cell_37_1207_end:
__sbr_cell_37_1208:
    mov rdi, r9
__sbr_cell_37_1208_end:
__sbr_cell_37_1209:
    sub rdi, rdx
__sbr_cell_37_1209_end:
__sbr_cell_37_1210:
    cmp rsi, rdi
__sbr_cell_37_1210_end:
__sbr_cell_37_1211:
    jge sbr_reset.L2580
__sbr_cell_37_1211_end:
__sbr_cell_37_1212:
    cmp rax, 64
__sbr_cell_37_1212_end:
__sbr_cell_37_1213:
    jae sbr_reset.L327a
__sbr_cell_37_1213_end:
__sbr_cell_37_1214:
    mov rsi, rax
__sbr_cell_37_1214_end:
__sbr_cell_37_1215:
    shl rsi, 4
__sbr_cell_37_1215_end:
__sbr_cell_37_1216:
    mov QWORD PTR [rbp+rsi*1-1392], rdx
__sbr_cell_37_1216_end:
__sbr_cell_37_1217:
    mov QWORD PTR [rbp+rsi*1-1384], r8
__sbr_cell_37_1217_end:
sbr_reset.L2562:
__sbr_cell_37_1218:
    add r9, 2
__sbr_cell_37_1218_end:
__sbr_cell_37_1219:
    mov rdx, r9
__sbr_cell_37_1219_end:
__sbr_cell_37_1220:
    inc rax
__sbr_cell_37_1220_end:
__sbr_cell_37_1221:
    jmp sbr_reset.L23c0
__sbr_cell_37_1221_end:
__sbr_cell_37_1222:
    .nops 1
__sbr_cell_37_1222_end:
sbr_reset.L2580:
__sbr_cell_37_1223:
    cmp rax, 64
__sbr_cell_37_1223_end:
__sbr_cell_37_1224:
    jae sbr_reset.L327f
__sbr_cell_37_1224_end:
__sbr_cell_37_1225:
    add r9, 2
__sbr_cell_37_1225_end:
__sbr_cell_37_1226:
    mov rsi, rax
__sbr_cell_37_1226_end:
__sbr_cell_37_1227:
    shl rsi, 4
__sbr_cell_37_1227_end:
__sbr_cell_37_1228:
    mov QWORD PTR [rbp+rsi*1-1392], r9
__sbr_cell_37_1228_end:
__sbr_cell_37_1229:
    mov QWORD PTR [rbp+rsi*1-1384], rcx
__sbr_cell_37_1229_end:
__sbr_cell_37_1230:
    mov rcx, r8
__sbr_cell_37_1230_end:
__sbr_cell_37_1231:
    inc rax
__sbr_cell_37_1231_end:
__sbr_cell_37_1232:
    jmp sbr_reset.L23c0
__sbr_cell_37_1232_end:
sbr_reset.L25b0:
__sbr_cell_37_1233:
    movzx esi, WORD PTR [rdx+0]
__sbr_cell_37_1233_end:
__sbr_cell_37_1234:
    movzx edi, WORD PTR [rcx+0]
__sbr_cell_37_1234_end:
__sbr_cell_37_1235:
    cmp si, di
__sbr_cell_37_1235_end:
__sbr_cell_37_1236:
    jle sbr_reset.L2390
__sbr_cell_37_1236_end:
__sbr_cell_37_1237:
    mov WORD PTR [rcx+0], si
__sbr_cell_37_1237_end:
__sbr_cell_37_1238:
    mov WORD PTR [rdx+0], di
__sbr_cell_37_1238_end:
__sbr_cell_37_1239:
    jmp sbr_reset.L2390
__sbr_cell_37_1239_end:
sbr_reset.L25ca:
__sbr_cell_37_1240:
    movsxd rcx, r13d
__sbr_cell_37_1240_end:
__sbr_cell_37_1241:
    jmp sbr_reset.L2619
__sbr_cell_37_1241_end:
sbr_reset.L25cf:
__sbr_cell_37_1242:
    cmp r13d, 49
__sbr_cell_37_1242_end:
__sbr_cell_37_1243:
    jae sbr_reset.L32d7
__sbr_cell_37_1243_end:
__sbr_cell_37_1244:
    movsx eax, WORD PTR [rbp-238]
__sbr_cell_37_1244_end:
__sbr_cell_37_1245:
    mov edi, DWORD PTR [rbp-80]
__sbr_cell_37_1245_end:
__sbr_cell_37_1246:
    sub edi, eax
__sbr_cell_37_1246_end:
__sbr_cell_37_1247:
    mov rsi, QWORD PTR [rbp-48]
__sbr_cell_37_1247_end:
__sbr_cell_37_1248:
    movsx ecx, WORD PTR [rbp+rsi*2-240]
__sbr_cell_37_1248_end:
__sbr_cell_37_1249:
    mov edx, ecx
__sbr_cell_37_1249_end:
__sbr_cell_37_1250:
    sub edx, eax
__sbr_cell_37_1250_end:
__sbr_cell_37_1251:
    sar edx, 1
__sbr_cell_37_1251_end:
__sbr_cell_37_1252:
    cmp edi, edx
__sbr_cell_37_1252_end:
__sbr_cell_37_1253:
    cmovl edx, edi
__sbr_cell_37_1253_end:
sbr_reset.L25fc:
__sbr_cell_37_1254:
    add eax, edx
__sbr_cell_37_1254_end:
__sbr_cell_37_1255:
    mov WORD PTR [rbp-238], ax
__sbr_cell_37_1255_end:
__sbr_cell_37_1256:
    sub ecx, edx
__sbr_cell_37_1256_end:
__sbr_cell_37_1257:
    mov WORD PTR [rbp+rsi*2-240], cx
__sbr_cell_37_1257_end:
__sbr_cell_37_1258:
    mov rcx, rsi
__sbr_cell_37_1258_end:
__sbr_cell_37_1259:
    lea rax, [rbp-238]
__sbr_cell_37_1259_end:
sbr_reset.L2619:
__sbr_cell_37_1260:
    mov QWORD PTR [rbp-1392], rax
__sbr_cell_37_1260_end:
__sbr_cell_37_1261:
    mov QWORD PTR [rbp-48], rcx
__sbr_cell_37_1261_end:
__sbr_cell_37_1262:
    lea rax, [rax+rcx*2+0]
__sbr_cell_37_1262_end:
__sbr_cell_37_1263:
    add rax, -2
__sbr_cell_37_1263_end:
sbr_reset.L262c:
__sbr_cell_37_1264:
    mov QWORD PTR [rbp-1384], rax
__sbr_cell_37_1264_end:
__sbr_cell_37_1265:
    mov eax, 1
__sbr_cell_37_1265_end:
__sbr_cell_37_1266:
    jmp sbr_reset.L2648
__sbr_cell_37_1266_end:
__sbr_cell_37_1267:
    .nops 1
__sbr_cell_37_1267_end:
sbr_reset.L2640:
__sbr_cell_37_1268:
    test eax, eax
__sbr_cell_37_1268_end:
__sbr_cell_37_1269:
    je sbr_reset.L287a
__sbr_cell_37_1269_end:
sbr_reset.L2648:
__sbr_cell_37_1270:
    cmp eax, 65
__sbr_cell_37_1270_end:
__sbr_cell_37_1271:
    jae sbr_reset.L3284
__sbr_cell_37_1271_end:
__sbr_cell_37_1272:
    dec eax
__sbr_cell_37_1272_end:
__sbr_cell_37_1273:
    mov rcx, rax
__sbr_cell_37_1273_end:
__sbr_cell_37_1274:
    shl rcx, 4
__sbr_cell_37_1274_end:
__sbr_cell_37_1275:
    mov rdx, QWORD PTR [rbp+rcx*1-1392]
__sbr_cell_37_1275_end:
__sbr_cell_37_1276:
    mov rcx, QWORD PTR [rbp+rcx*1-1384]
__sbr_cell_37_1276_end:
__sbr_cell_37_1277:
    .nops 1
__sbr_cell_37_1277_end:
sbr_reset.L2670:
__sbr_cell_37_1278:
    cmp rdx, rcx
__sbr_cell_37_1278_end:
__sbr_cell_37_1279:
    jae sbr_reset.L2640
__sbr_cell_37_1279_end:
__sbr_cell_37_1280:
    lea rdi, [rcx-2]
__sbr_cell_37_1280_end:
__sbr_cell_37_1281:
    cmp rdx, rdi
__sbr_cell_37_1281_end:
__sbr_cell_37_1282:
    jae sbr_reset.L2860
__sbr_cell_37_1282_end:
__sbr_cell_37_1283:
    mov r8, rcx
__sbr_cell_37_1283_end:
__sbr_cell_37_1284:
    sub r8, rdx
__sbr_cell_37_1284_end:
__sbr_cell_37_1285:
    sar r8, 2
__sbr_cell_37_1285_end:
__sbr_cell_37_1286:
    lea rsi, [rdx+r8*2+0]
__sbr_cell_37_1286_end:
__sbr_cell_37_1287:
    movzx r9d, WORD PTR [rdx+0]
__sbr_cell_37_1287_end:
__sbr_cell_37_1288:
    movzx r11d, WORD PTR [rcx+0]
__sbr_cell_37_1288_end:
__sbr_cell_37_1289:
    movzx r8d, WORD PTR [rdx+r8*2+0]
__sbr_cell_37_1289_end:
sbr_reset.L269d:
__sbr_cell_37_1290:
    cmp r9w, r11w
__sbr_cell_37_1290_end:
__sbr_cell_37_1291:
    jle sbr_reset.L26c0
__sbr_cell_37_1291_end:
__sbr_cell_37_1292:
    cmp r11w, r8w
__sbr_cell_37_1292_end:
__sbr_cell_37_1293:
    jg sbr_reset.L26cc
__sbr_cell_37_1293_end:
__sbr_cell_37_1294:
    mov WORD PTR [rcx+0], r9w
__sbr_cell_37_1294_end:
__sbr_cell_37_1295:
    mov r8d, r11d
__sbr_cell_37_1295_end:
__sbr_cell_37_1296:
    jmp sbr_reset.L26d0
__sbr_cell_37_1296_end:
__sbr_cell_37_1297:
    .nops 1
__sbr_cell_37_1297_end:
sbr_reset.L26c0:
__sbr_cell_37_1298:
    mov r10d, 1
__sbr_cell_37_1298_end:
__sbr_cell_37_1299:
    cmp r9w, r8w
__sbr_cell_37_1299_end:
__sbr_cell_37_1300:
    jle sbr_reset.L26df
__sbr_cell_37_1300_end:
sbr_reset.L26cc:
__sbr_cell_37_1301:
    mov WORD PTR [rsi+0], r9w
__sbr_cell_37_1301_end:
sbr_reset.L26d0:
__sbr_cell_37_1302:
    mov WORD PTR [rdx+0], r8w
__sbr_cell_37_1302_end:
__sbr_cell_37_1303:
    movzx r8d, WORD PTR [rsi+0]
__sbr_cell_37_1303_end:
__sbr_cell_37_1304:
    movzx r11d, WORD PTR [rcx+0]
__sbr_cell_37_1304_end:
__sbr_cell_37_1305:
    xor r10d, r10d
__sbr_cell_37_1305_end:
sbr_reset.L26df:
__sbr_cell_37_1306:
    cmp r8w, r11w
__sbr_cell_37_1306_end:
__sbr_cell_37_1307:
    jle sbr_reset.L2700
__sbr_cell_37_1307_end:
__sbr_cell_37_1308:
    mov WORD PTR [rcx+0], r8w
__sbr_cell_37_1308_end:
__sbr_cell_37_1309:
    mov WORD PTR [rsi+0], r11w
__sbr_cell_37_1309_end:
__sbr_cell_37_1310:
    xor r10d, r10d
__sbr_cell_37_1310_end:
__sbr_cell_37_1311:
    lea r8, [rcx-4]
__sbr_cell_37_1311_end:
__sbr_cell_37_1312:
    cmp rdx, r8
__sbr_cell_37_1312_end:
__sbr_cell_37_1313:
    jne sbr_reset.L2710
__sbr_cell_37_1313_end:
__sbr_cell_37_1314:
    jmp sbr_reset.L2640
__sbr_cell_37_1314_end:
__sbr_cell_37_1315:
    .nops 1
__sbr_cell_37_1315_end:
sbr_reset.L2700:
__sbr_cell_37_1316:
    mov r11d, r8d
__sbr_cell_37_1316_end:
__sbr_cell_37_1317:
    lea r8, [rcx-4]
__sbr_cell_37_1317_end:
__sbr_cell_37_1318:
    cmp rdx, r8
__sbr_cell_37_1318_end:
__sbr_cell_37_1319:
    je sbr_reset.L2640
__sbr_cell_37_1319_end:
sbr_reset.L2710:
__sbr_cell_37_1320:
    lea r9, [rdx+2]
__sbr_cell_37_1320_end:
__sbr_cell_37_1321:
    movzx ebx, WORD PTR [rdi+0]
__sbr_cell_37_1321_end:
__sbr_cell_37_1322:
    mov WORD PTR [rsi+0], bx
__sbr_cell_37_1322_end:
__sbr_cell_37_1323:
    mov WORD PTR [rdi+0], r11w
__sbr_cell_37_1323_end:
__sbr_cell_37_1324:
    cmp r9, r8
__sbr_cell_37_1324_end:
__sbr_cell_37_1325:
    jbe sbr_reset.L2749
__sbr_cell_37_1325_end:
__sbr_cell_37_1326:
    jmp sbr_reset.L2794
__sbr_cell_37_1326_end:
__sbr_cell_37_1327:
    .nops 1
__sbr_cell_37_1327_end:
sbr_reset.L2730:
__sbr_cell_37_1328:
    movzx r11d, WORD PTR [r9+0]
__sbr_cell_37_1328_end:
__sbr_cell_37_1329:
    mov WORD PTR [r8+0], r11w
__sbr_cell_37_1329_end:
__sbr_cell_37_1330:
    mov WORD PTR [r9+0], r14w
__sbr_cell_37_1330_end:
__sbr_cell_37_1331:
    add r9, 2
__sbr_cell_37_1331_end:
__sbr_cell_37_1332:
    add r8, -2
__sbr_cell_37_1332_end:
sbr_reset.L2744:
__sbr_cell_37_1333:
    cmp r9, r8
__sbr_cell_37_1333_end:
__sbr_cell_37_1334:
    ja sbr_reset.L2790
__sbr_cell_37_1334_end:
sbr_reset.L2749:
__sbr_cell_37_1335:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_1335_end:
__sbr_cell_37_1336:
    .nops 1
__sbr_cell_37_1336_end:
sbr_reset.L2750:
__sbr_cell_37_1337:
    cmp WORD PTR [r9+0], r11w
__sbr_cell_37_1337_end:
__sbr_cell_37_1338:
    jge sbr_reset.L2774
__sbr_cell_37_1338_end:
__sbr_cell_37_1339:
    add r9, 2
__sbr_cell_37_1339_end:
__sbr_cell_37_1340:
    cmp r9, r8
__sbr_cell_37_1340_end:
__sbr_cell_37_1341:
    jbe sbr_reset.L2750
__sbr_cell_37_1341_end:
__sbr_cell_37_1342:
    jmp sbr_reset.L2774
__sbr_cell_37_1342_end:
__sbr_cell_37_1343:
    .nops 1
__sbr_cell_37_1343_end:
sbr_reset.L2770:
__sbr_cell_37_1344:
    add r8, -2
__sbr_cell_37_1344_end:
sbr_reset.L2774:
__sbr_cell_37_1345:
    cmp r9, r8
__sbr_cell_37_1345_end:
__sbr_cell_37_1346:
    ja sbr_reset.L2744
__sbr_cell_37_1346_end:
__sbr_cell_37_1347:
    movzx r14d, WORD PTR [r8+0]
__sbr_cell_37_1347_end:
__sbr_cell_37_1348:
    cmp r14w, r11w
__sbr_cell_37_1348_end:
__sbr_cell_37_1349:
    jg sbr_reset.L2770
__sbr_cell_37_1349_end:
__sbr_cell_37_1350:
    jmp sbr_reset.L2730
__sbr_cell_37_1350_end:
__sbr_cell_37_1351:
    .nops 1
__sbr_cell_37_1351_end:
sbr_reset.L2790:
__sbr_cell_37_1352:
    movzx r11d, WORD PTR [rdi+0]
__sbr_cell_37_1352_end:
sbr_reset.L2794:
__sbr_cell_37_1353:
    movzx ebx, WORD PTR [r9+0]
__sbr_cell_37_1353_end:
__sbr_cell_37_1354:
    mov WORD PTR [r9+0], r11w
__sbr_cell_37_1354_end:
__sbr_cell_37_1355:
    mov WORD PTR [rdi+0], bx
__sbr_cell_37_1355_end:
__sbr_cell_37_1356:
    test r10d, r10d
__sbr_cell_37_1356_end:
__sbr_cell_37_1357:
    je sbr_reset.L27e0
__sbr_cell_37_1357_end:
__sbr_cell_37_1358:
    cmp rsi, r9
__sbr_cell_37_1358_end:
__sbr_cell_37_1359:
    je sbr_reset.L27b2
__sbr_cell_37_1359_end:
__sbr_cell_37_1360:
    lea rdi, [r9-2]
__sbr_cell_37_1360_end:
__sbr_cell_37_1361:
    cmp rsi, rdi
__sbr_cell_37_1361_end:
__sbr_cell_37_1362:
    jne sbr_reset.L27e0
__sbr_cell_37_1362_end:
sbr_reset.L27b2:
__sbr_cell_37_1363:
    mov rdi, rdx
__sbr_cell_37_1363_end:
__sbr_cell_37_1364:
    .nops 1
__sbr_cell_37_1364_end:
sbr_reset.L27c0:
__sbr_cell_37_1365:
    mov rsi, rdi
__sbr_cell_37_1365_end:
__sbr_cell_37_1366:
    cmp rdi, rcx
__sbr_cell_37_1366_end:
__sbr_cell_37_1367:
    jae sbr_reset.L27d7
__sbr_cell_37_1367_end:
__sbr_cell_37_1368:
    lea rdi, [rsi+2]
__sbr_cell_37_1368_end:
__sbr_cell_37_1369:
    movzx r10d, WORD PTR [rsi+0]
__sbr_cell_37_1369_end:
__sbr_cell_37_1370:
    cmp r10w, WORD PTR [rsi+2]
__sbr_cell_37_1370_end:
__sbr_cell_37_1371:
    jle sbr_reset.L27c0
__sbr_cell_37_1371_end:
sbr_reset.L27d7:
__sbr_cell_37_1372:
    cmp rsi, rcx
__sbr_cell_37_1372_end:
__sbr_cell_37_1373:
    je sbr_reset.L2640
__sbr_cell_37_1373_end:
sbr_reset.L27e0:
__sbr_cell_37_1374:
    mov rsi, rcx
__sbr_cell_37_1374_end:
__sbr_cell_37_1375:
    sub rsi, r9
__sbr_cell_37_1375_end:
__sbr_cell_37_1376:
    mov rdi, r9
__sbr_cell_37_1376_end:
__sbr_cell_37_1377:
    sub rdi, rdx
__sbr_cell_37_1377_end:
__sbr_cell_37_1378:
    cmp rsi, rdi
__sbr_cell_37_1378_end:
__sbr_cell_37_1379:
    jge sbr_reset.L2830
__sbr_cell_37_1379_end:
__sbr_cell_37_1380:
    cmp rax, 64
__sbr_cell_37_1380_end:
__sbr_cell_37_1381:
    jae sbr_reset.L3270
__sbr_cell_37_1381_end:
__sbr_cell_37_1382:
    mov rsi, rax
__sbr_cell_37_1382_end:
__sbr_cell_37_1383:
    shl rsi, 4
__sbr_cell_37_1383_end:
__sbr_cell_37_1384:
    mov QWORD PTR [rbp+rsi*1-1392], rdx
__sbr_cell_37_1384_end:
__sbr_cell_37_1385:
    mov QWORD PTR [rbp+rsi*1-1384], r8
__sbr_cell_37_1385_end:
sbr_reset.L2812:
__sbr_cell_37_1386:
    add r9, 2
__sbr_cell_37_1386_end:
__sbr_cell_37_1387:
    mov rdx, r9
__sbr_cell_37_1387_end:
__sbr_cell_37_1388:
    inc rax
__sbr_cell_37_1388_end:
__sbr_cell_37_1389:
    jmp sbr_reset.L2670
__sbr_cell_37_1389_end:
__sbr_cell_37_1390:
    .nops 1
__sbr_cell_37_1390_end:
sbr_reset.L2830:
__sbr_cell_37_1391:
    cmp rax, 64
__sbr_cell_37_1391_end:
__sbr_cell_37_1392:
    jae sbr_reset.L3275
__sbr_cell_37_1392_end:
__sbr_cell_37_1393:
    add r9, 2
__sbr_cell_37_1393_end:
__sbr_cell_37_1394:
    mov rsi, rax
__sbr_cell_37_1394_end:
__sbr_cell_37_1395:
    shl rsi, 4
__sbr_cell_37_1395_end:
__sbr_cell_37_1396:
    mov QWORD PTR [rbp+rsi*1-1392], r9
__sbr_cell_37_1396_end:
__sbr_cell_37_1397:
    mov QWORD PTR [rbp+rsi*1-1384], rcx
__sbr_cell_37_1397_end:
__sbr_cell_37_1398:
    mov rcx, r8
__sbr_cell_37_1398_end:
__sbr_cell_37_1399:
    inc rax
__sbr_cell_37_1399_end:
__sbr_cell_37_1400:
    jmp sbr_reset.L2670
__sbr_cell_37_1400_end:
sbr_reset.L2860:
__sbr_cell_37_1401:
    movzx esi, WORD PTR [rdx+0]
__sbr_cell_37_1401_end:
__sbr_cell_37_1402:
    movzx edi, WORD PTR [rcx+0]
__sbr_cell_37_1402_end:
__sbr_cell_37_1403:
    cmp si, di
__sbr_cell_37_1403_end:
__sbr_cell_37_1404:
    jle sbr_reset.L2640
__sbr_cell_37_1404_end:
__sbr_cell_37_1405:
    mov WORD PTR [rcx+0], si
__sbr_cell_37_1405_end:
__sbr_cell_37_1406:
    mov WORD PTR [rdx+0], di
__sbr_cell_37_1406_end:
__sbr_cell_37_1407:
    jmp sbr_reset.L2640
__sbr_cell_37_1407_end:
sbr_reset.L287a:
__sbr_cell_37_1408:
    movzx eax, WORD PTR [r12+68]
__sbr_cell_37_1408_end:
__sbr_cell_37_1409:
    mov WORD PTR [rbp-240], ax
__sbr_cell_37_1409_end:
__sbr_cell_37_1410:
    test r13d, r13d
__sbr_cell_37_1410_end:
__sbr_cell_37_1411:
    jle sbr_reset.L2949
__sbr_cell_37_1411_end:
__sbr_cell_37_1412:
    add r15d, r15d
__sbr_cell_37_1412_end:
__sbr_cell_37_1413:
    neg r15
__sbr_cell_37_1413_end:
__sbr_cell_37_1414:
    mov ecx, 4
__sbr_cell_37_1414_end:
sbr_reset.L289b:
__sbr_cell_37_1415:
    cmp rcx, 52
__sbr_cell_37_1415_end:
__sbr_cell_37_1416:
    je sbr_reset.L32c3
__sbr_cell_37_1416_end:
__sbr_cell_37_1417:
    movzx eax, WORD PTR [rbp+rcx*2-246]
__sbr_cell_37_1417_end:
__sbr_cell_37_1418:
    test ax, ax
__sbr_cell_37_1418_end:
__sbr_cell_37_1419:
    jle sbr_reset.L29cd
__sbr_cell_37_1419_end:
__sbr_cell_37_1420:
    add ax, WORD PTR [rbp+rcx*2-248]
__sbr_cell_37_1420_end:
__sbr_cell_37_1421:
    mov WORD PTR [rbp+rcx*2-246], ax
__sbr_cell_37_1421_end:
__sbr_cell_37_1422:
    movzx eax, WORD PTR [rbp+rcx*2-244]
__sbr_cell_37_1422_end:
__sbr_cell_37_1423:
    test ax, ax
__sbr_cell_37_1423_end:
__sbr_cell_37_1424:
    jle sbr_reset.L29d3
__sbr_cell_37_1424_end:
__sbr_cell_37_1425:
    add ax, WORD PTR [rbp+rcx*2-246]
__sbr_cell_37_1425_end:
__sbr_cell_37_1426:
    mov WORD PTR [rbp+rcx*2-244], ax
__sbr_cell_37_1426_end:
sbr_reset.L28e7:
__sbr_cell_37_1427:
    lea rax, [r15+rcx*1+0]
__sbr_cell_37_1427_end:
__sbr_cell_37_1428:
    cmp rax, 2
__sbr_cell_37_1428_end:
__sbr_cell_37_1429:
    je sbr_reset.L2949
__sbr_cell_37_1429_end:
__sbr_cell_37_1430:
    movzx eax, WORD PTR [rbp+rcx*2-242]
__sbr_cell_37_1430_end:
__sbr_cell_37_1431:
    test ax, ax
__sbr_cell_37_1431_end:
__sbr_cell_37_1432:
    jle sbr_reset.L29d9
__sbr_cell_37_1432_end:
__sbr_cell_37_1433:
    add ax, WORD PTR [rbp+rcx*2-244]
__sbr_cell_37_1433_end:
__sbr_cell_37_1434:
    mov WORD PTR [rbp+rcx*2-242], ax
__sbr_cell_37_1434_end:
__sbr_cell_37_1435:
    movzx eax, WORD PTR [rbp+rcx*2-240]
__sbr_cell_37_1435_end:
__sbr_cell_37_1436:
    test ax, ax
__sbr_cell_37_1436_end:
__sbr_cell_37_1437:
    jle sbr_reset.L29dc
__sbr_cell_37_1437_end:
__sbr_cell_37_1438:
    add ax, WORD PTR [rbp+rcx*2-242]
__sbr_cell_37_1438_end:
sbr_reset.L292b:
__sbr_cell_37_1439:
    mov WORD PTR [rbp+rcx*2-240], ax
__sbr_cell_37_1439_end:
__sbr_cell_37_1440:
    lea rax, [r15+rcx*1+0]
__sbr_cell_37_1440_end:
__sbr_cell_37_1441:
    add rax, 4
__sbr_cell_37_1441_end:
__sbr_cell_37_1442:
    add rcx, 4
__sbr_cell_37_1442_end:
__sbr_cell_37_1443:
    cmp rax, 4
__sbr_cell_37_1443_end:
__sbr_cell_37_1444:
    jne sbr_reset.L289b
__sbr_cell_37_1444_end:
sbr_reset.L2949:
__sbr_cell_37_1445:
    add r13d, DWORD PTR [rbp-72]
__sbr_cell_37_1445_end:
__sbr_cell_37_1446:
    mov DWORD PTR [r12+104], r13d
__sbr_cell_37_1446_end:
__sbr_cell_37_1447:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_1447_end:
__sbr_cell_37_1448:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_1448_end:
__sbr_cell_37_1449:
    jle sbr_reset.L29b9
__sbr_cell_37_1449_end:
__sbr_cell_37_1450:
    movzx r14d, BYTE PTR [r12+30]
__sbr_cell_37_1450_end:
__sbr_cell_37_1451:
    movzx ecx, r14b
__sbr_cell_37_1451_end:
__sbr_cell_37_1452:
    cmp r13d, ecx
__sbr_cell_37_1452_end:
__sbr_cell_37_1453:
    jbe sbr_reset.L29ad
__sbr_cell_37_1453_end:
__sbr_cell_37_1454:
    lea rdi, [r12+311792]
__sbr_cell_37_1454_end:
__sbr_cell_37_1455:
    mov rbx, QWORD PTR [rbp-136]
__sbr_cell_37_1455_end:
__sbr_cell_37_1456:
    lea rdx, [rbx+rbx*1+0]
__sbr_cell_37_1456_end:
sbr_reset.L297e:
__sbr_cell_37_1457:
    lea rsi, [rbp-368]
__sbr_cell_37_1457_end:
__sbr_cell_37_1458:
    call memcpy
__sbr_cell_37_1458_end:
sbr_reset.L298a:
__sbr_cell_37_1459:
    lea rdi, [r12+rbx*2+0]
__sbr_cell_37_1459_end:
__sbr_cell_37_1460:
    add rdi, 311792
__sbr_cell_37_1460_end:
__sbr_cell_37_1461:
    mov rdx, QWORD PTR [rbp-48]
__sbr_cell_37_1461_end:
__sbr_cell_37_1462:
    add rdx, rdx
__sbr_cell_37_1462_end:
__sbr_cell_37_1463:
    lea rsi, [rbp-238]
__sbr_cell_37_1463_end:
sbr_reset.L29a3:
__sbr_cell_37_1464:
    call memcpy
__sbr_cell_37_1464_end:
sbr_reset.L29a8:
__sbr_cell_37_1465:
    jmp sbr_reset.L2012
__sbr_cell_37_1465_end:
sbr_reset.L29ad:
__sbr_cell_37_1466:
    lea rdx, [rip+L_str_15]
__sbr_cell_37_1466_end:
__sbr_cell_37_1467:
    jmp sbr_reset.L167a
__sbr_cell_37_1467_end:
sbr_reset.L29b9:
__sbr_cell_37_1468:
    lea rdx, [rip+L_str_14]
__sbr_cell_37_1468_end:
__sbr_cell_37_1469:
    mov esi, 16
__sbr_cell_37_1469_end:
__sbr_cell_37_1470:
    mov ecx, r13d
__sbr_cell_37_1470_end:
__sbr_cell_37_1471:
    jmp sbr_reset.L1d2a
__sbr_cell_37_1471_end:
sbr_reset.L29cd:
__sbr_cell_37_1472:
    add rcx, -3
__sbr_cell_37_1472_end:
__sbr_cell_37_1473:
    jmp sbr_reset.L29dc
__sbr_cell_37_1473_end:
sbr_reset.L29d3:
__sbr_cell_37_1474:
    add rcx, -2
__sbr_cell_37_1474_end:
__sbr_cell_37_1475:
    jmp sbr_reset.L29dc
__sbr_cell_37_1475_end:
sbr_reset.L29d9:
__sbr_cell_37_1476:
    dec rcx
__sbr_cell_37_1476_end:
sbr_reset.L29dc:
__sbr_cell_37_1477:
    movsx r8d, ax
__sbr_cell_37_1477_end:
__sbr_cell_37_1478:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_1478_end:
__sbr_cell_37_1479:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_1479_end:
__sbr_cell_37_1480:
    lea rdx, [rip+L_str_13]
__sbr_cell_37_1480_end:
__sbr_cell_37_1481:
    jmp sbr_reset.L1cff
__sbr_cell_37_1481_end:
sbr_reset.L29f4:
__sbr_cell_37_1482:
    mov eax, r15d
__sbr_cell_37_1482_end:
__sbr_cell_37_1483:
    and eax, 15
__sbr_cell_37_1483_end:
__sbr_cell_37_1484:
    mov edx, 16
__sbr_cell_37_1484_end:
__sbr_cell_37_1485:
    cmovne rdx, rax
__sbr_cell_37_1485_end:
__sbr_cell_37_1486:
    mov r9, r15
__sbr_cell_37_1486_end:
__sbr_cell_37_1487:
    sub r9, rdx
__sbr_cell_37_1487_end:
__sbr_cell_37_1488:
    lea rax, [r9+1]
__sbr_cell_37_1488_end:
__sbr_cell_37_1489:
    lea edi, [r13*2+0]
__sbr_cell_37_1489_end:
__sbr_cell_37_1490:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_37_1490_end:
__sbr_cell_37_1491:
    mov rsi, r8
__sbr_cell_37_1491_end:
__sbr_cell_37_1492:
    sub rsi, rdi
__sbr_cell_37_1492_end:
__sbr_cell_37_1493:
    add rsi, 311992
__sbr_cell_37_1493_end:
sbr_reset.L2a26:
__sbr_cell_37_1494:
    xor edi, edi
__sbr_cell_37_1494_end:
__sbr_cell_37_1495:
    vmovdqa xmm0, XMMWORD PTR [rip+LCPI5_6]
__sbr_cell_37_1495_end:
sbr_reset.L2a30:
__sbr_cell_37_1496:
    vmovdqu xmm1, XMMWORD PTR [rsi+rdi*4-48]
__sbr_cell_37_1496_end:
__sbr_cell_37_1497:
    vmovdqu xmm2, XMMWORD PTR [rsi+rdi*4-32]
__sbr_cell_37_1497_end:
__sbr_cell_37_1498:
    vmovdqu xmm3, XMMWORD PTR [rsi+rdi*4-16]
__sbr_cell_37_1498_end:
__sbr_cell_37_1499:
    vmovdqu xmm4, XMMWORD PTR [rsi+rdi*4+0]
__sbr_cell_37_1499_end:
__sbr_cell_37_1500:
    vpshufb xmm1, xmm1, xmm0
__sbr_cell_37_1500_end:
__sbr_cell_37_1501:
    vpshufb xmm2, xmm2, xmm0
__sbr_cell_37_1501_end:
__sbr_cell_37_1502:
    vpunpcklqdq xmm1, xmm1, xmm2
__sbr_cell_37_1502_end:
__sbr_cell_37_1503:
    vmovdqu XMMWORD PTR [r8+rdi*2+311892], xmm1
__sbr_cell_37_1503_end:
__sbr_cell_37_1504:
    vpshufb xmm1, xmm3, xmm0
__sbr_cell_37_1504_end:
__sbr_cell_37_1505:
    vpshufb xmm2, xmm4, xmm0
__sbr_cell_37_1505_end:
__sbr_cell_37_1506:
    vpunpcklqdq xmm1, xmm1, xmm2
__sbr_cell_37_1506_end:
__sbr_cell_37_1507:
    vmovdqu XMMWORD PTR [r8+rdi*2+311908], xmm1
__sbr_cell_37_1507_end:
sbr_reset.L2a77:
__sbr_cell_37_1508:
    add rdi, 16
__sbr_cell_37_1508_end:
__sbr_cell_37_1509:
    cmp r9, rdi
__sbr_cell_37_1509_end:
__sbr_cell_37_1510:
    jne sbr_reset.L2a30
__sbr_cell_37_1510_end:
__sbr_cell_37_1511:
    cmp edx, 5
__sbr_cell_37_1511_end:
__sbr_cell_37_1512:
    jb sbr_reset.L2aef
__sbr_cell_37_1512_end:
sbr_reset.L2a85:
__sbr_cell_37_1513:
    mov eax, r15d
__sbr_cell_37_1513_end:
__sbr_cell_37_1514:
    and eax, 3
__sbr_cell_37_1514_end:
__sbr_cell_37_1515:
    mov esi, 4
__sbr_cell_37_1515_end:
__sbr_cell_37_1516:
    cmovne rsi, rax
__sbr_cell_37_1516_end:
__sbr_cell_37_1517:
    mov rdx, r15
__sbr_cell_37_1517_end:
__sbr_cell_37_1518:
    sub rdx, rsi
__sbr_cell_37_1518_end:
__sbr_cell_37_1519:
    neg rsi
__sbr_cell_37_1519_end:
__sbr_cell_37_1520:
    lea rax, [r15+rsi*1+0]
__sbr_cell_37_1520_end:
__sbr_cell_37_1521:
    inc rax
__sbr_cell_37_1521_end:
__sbr_cell_37_1522:
    sub rdx, r9
__sbr_cell_37_1522_end:
__sbr_cell_37_1523:
    mov r8, QWORD PTR [rbp-48]
__sbr_cell_37_1523_end:
__sbr_cell_37_1524:
    lea rsi, [r8+r9*2+0]
__sbr_cell_37_1524_end:
sbr_reset.L2aaf:
__sbr_cell_37_1525:
    add rsi, 311892
__sbr_cell_37_1525_end:
__sbr_cell_37_1526:
    lea edi, [r13*2+0]
__sbr_cell_37_1526_end:
__sbr_cell_37_1527:
    lea r8, [r8+r9*4+0]
__sbr_cell_37_1527_end:
__sbr_cell_37_1528:
    sub r8, rdi
__sbr_cell_37_1528_end:
__sbr_cell_37_1529:
    add r8, 311944
__sbr_cell_37_1529_end:
__sbr_cell_37_1530:
    xor edi, edi
__sbr_cell_37_1530_end:
__sbr_cell_37_1531:
    vmovq xmm0, QWORD PTR [rip+LCPI5_9]
__sbr_cell_37_1531_end:
sbr_reset.L2ad6:
__sbr_cell_37_1532:
    vmovdqu xmm1, XMMWORD PTR [r8+rdi*4+0]
__sbr_cell_37_1532_end:
__sbr_cell_37_1533:
    vpshufb xmm1, xmm1, xmm0
__sbr_cell_37_1533_end:
__sbr_cell_37_1534:
    vmovq QWORD PTR [rsi+rdi*2+0], xmm1
__sbr_cell_37_1534_end:
__sbr_cell_37_1535:
    add rdi, 4
__sbr_cell_37_1535_end:
__sbr_cell_37_1536:
    cmp rdx, rdi
__sbr_cell_37_1536_end:
__sbr_cell_37_1537:
    jne sbr_reset.L2ad6
__sbr_cell_37_1537_end:
sbr_reset.L2aef:
__sbr_cell_37_1538:
    mov r8, r15
__sbr_cell_37_1538_end:
__sbr_cell_37_1539:
    sub r8, rax
__sbr_cell_37_1539_end:
__sbr_cell_37_1540:
    inc r8
__sbr_cell_37_1540_end:
__sbr_cell_37_1541:
    mov rsi, QWORD PTR [rbp-48]
__sbr_cell_37_1541_end:
__sbr_cell_37_1542:
    lea rdx, [rsi+rax*2+0]
__sbr_cell_37_1542_end:
__sbr_cell_37_1543:
    add rdx, 311890
__sbr_cell_37_1543_end:
__sbr_cell_37_1544:
    add r13d, r13d
__sbr_cell_37_1544_end:
__sbr_cell_37_1545:
    lea rax, [rsi+rax*4+0]
__sbr_cell_37_1545_end:
__sbr_cell_37_1546:
    sub rax, r13
__sbr_cell_37_1546_end:
__sbr_cell_37_1547:
    add rax, 311940
__sbr_cell_37_1547_end:
__sbr_cell_37_1548:
    xor esi, esi
__sbr_cell_37_1548_end:
__sbr_cell_37_1549:
    .nops 1
__sbr_cell_37_1549_end:
sbr_reset.L2b20:
__sbr_cell_37_1550:
    movzx edi, WORD PTR [rax+rsi*4+0]
__sbr_cell_37_1550_end:
__sbr_cell_37_1551:
    mov WORD PTR [rdx+rsi*2+0], di
__sbr_cell_37_1551_end:
__sbr_cell_37_1552:
    inc rsi
__sbr_cell_37_1552_end:
__sbr_cell_37_1553:
    cmp r8, rsi
__sbr_cell_37_1553_end:
__sbr_cell_37_1554:
    jne sbr_reset.L2b20
__sbr_cell_37_1554_end:
sbr_reset.L2b30:
__sbr_cell_37_1555:
    mov DWORD PTR [rbp-128], r10d
__sbr_cell_37_1555_end:
__sbr_cell_37_1556:
    mov DWORD PTR [rbp-80], ecx
__sbr_cell_37_1556_end:
__sbr_cell_37_1557:
    mov r12, QWORD PTR [rbp-48]
__sbr_cell_37_1557_end:
__sbr_cell_37_1558:
    movzx eax, BYTE PTR [r12+33]
__sbr_cell_37_1558_end:
__sbr_cell_37_1559:
    vcvtsi2ss xmm0, xmm15, eax
__sbr_cell_37_1559_end:
sbr_reset.L2b45:
__sbr_cell_37_1560:
    vmovss DWORD PTR [rbp-72], xmm0
__sbr_cell_37_1560_end:
__sbr_cell_37_1561:
    mov eax, DWORD PTR [r12+72]
__sbr_cell_37_1561_end:
__sbr_cell_37_1562:
    vcvtsi2ss xmm0, xmm15, rax
__sbr_cell_37_1562_end:
__sbr_cell_37_1563:
    movsx eax, r14w
__sbr_cell_37_1563_end:
__sbr_cell_37_1564:
    vcvtsi2ss xmm1, xmm15, eax
__sbr_cell_37_1564_end:
__sbr_cell_37_1565:
    vdivss xmm0, xmm0, xmm1
__sbr_cell_37_1565_end:
sbr_reset.L2b60:
__sbr_cell_37_1566:
    call log2f
__sbr_cell_37_1566_end:
sbr_reset.L2b65:
__sbr_cell_37_1567:
    vmulss xmm0, xmm0, DWORD PTR [rbp-72]
__sbr_cell_37_1567_end:
__sbr_cell_37_1568:
    vcvtss2si rax, xmm0
__sbr_cell_37_1568_end:
__sbr_cell_37_1569:
    cmp rax, 2
__sbr_cell_37_1569_end:
__sbr_cell_37_1570:
    mov ecx, 1
__sbr_cell_37_1570_end:
__sbr_cell_37_1571:
    cmovge rcx, rax
__sbr_cell_37_1571_end:
__sbr_cell_37_1572:
    mov DWORD PTR [r12+311784], ecx
__sbr_cell_37_1572_end:
__sbr_cell_37_1573:
    cmp ecx, 6
__sbr_cell_37_1573_end:
__sbr_cell_37_1574:
    jb sbr_reset.L2bb5
__sbr_cell_37_1574_end:
__sbr_cell_37_1575:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_1575_end:
__sbr_cell_37_1576:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_1576_end:
__sbr_cell_37_1577:
    lea rdx, [rip+L_str_18]
__sbr_cell_37_1577_end:
__sbr_cell_37_1578:
    mov esi, 16
__sbr_cell_37_1578_end:
sbr_reset.L2b9d:
__sbr_cell_37_1579:
    xor eax, eax
__sbr_cell_37_1579_end:
__sbr_cell_37_1580:
    call av_log
__sbr_cell_37_1580_end:
sbr_reset.L2ba4:
__sbr_cell_37_1581:
    mov DWORD PTR [r12+311784], 1
__sbr_cell_37_1581_end:
__sbr_cell_37_1582:
    jmp sbr_reset.L1d31
__sbr_cell_37_1582_end:
sbr_reset.L2bb5:
__sbr_cell_37_1583:
    mov WORD PTR [r12+312038], r14w
__sbr_cell_37_1583_end:
__sbr_cell_37_1584:
    test ecx, ecx
__sbr_cell_37_1584_end:
__sbr_cell_37_1585:
    mov r11, QWORD PTR [rbp-56]
__sbr_cell_37_1585_end:
__sbr_cell_37_1586:
    je sbr_reset.L2c89
__sbr_cell_37_1586_end:
__sbr_cell_37_1587:
    mov eax, ecx
__sbr_cell_37_1587_end:
__sbr_cell_37_1588:
    and eax, 7
__sbr_cell_37_1588_end:
__sbr_cell_37_1589:
    cmp eax, 1
__sbr_cell_37_1589_end:
__sbr_cell_37_1590:
    jne sbr_reset.L2bde
__sbr_cell_37_1590_end:
__sbr_cell_37_1591:
    xor esi, esi
__sbr_cell_37_1591_end:
__sbr_cell_37_1592:
    mov r8d, 1
__sbr_cell_37_1592_end:
__sbr_cell_37_1593:
    jmp sbr_reset.L2c5b
__sbr_cell_37_1593_end:
sbr_reset.L2bde:
__sbr_cell_37_1594:
    mov r9d, ecx
__sbr_cell_37_1594_end:
__sbr_cell_37_1595:
    and r9d, 6
__sbr_cell_37_1595_end:
__sbr_cell_37_1596:
    xor esi, esi
__sbr_cell_37_1596_end:
__sbr_cell_37_1597:
    mov r10d, ecx
__sbr_cell_37_1597_end:
__sbr_cell_37_1598:
    xor r8d, r8d
__sbr_cell_37_1598_end:
sbr_reset.L2bed:
__sbr_cell_37_1599:
    mov eax, r15d
__sbr_cell_37_1599_end:
__sbr_cell_37_1600:
    sub eax, esi
__sbr_cell_37_1600_end:
__sbr_cell_37_1601:
    xor edx, edx
__sbr_cell_37_1601_end:
__sbr_cell_37_1602:
    div r10d
__sbr_cell_37_1602_end:
__sbr_cell_37_1603:
    mov edi, eax
__sbr_cell_37_1603_end:
__sbr_cell_37_1604:
    add edi, esi
__sbr_cell_37_1604_end:
__sbr_cell_37_1605:
    cmp edi, 25
__sbr_cell_37_1605_end:
__sbr_cell_37_1606:
    jae sbr_reset.L32b9
__sbr_cell_37_1606_end:
__sbr_cell_37_1607:
    mov eax, edi
__sbr_cell_37_1607_end:
__sbr_cell_37_1608:
    movzx eax, WORD PTR [r12+rax*2+311890]
__sbr_cell_37_1608_end:
__sbr_cell_37_1609:
    mov WORD PTR [r12+r8*2+312040], ax
__sbr_cell_37_1609_end:
__sbr_cell_37_1610:
    mov eax, r15d
__sbr_cell_37_1610_end:
sbr_reset.L2c1b:
__sbr_cell_37_1611:
    sub eax, edi
__sbr_cell_37_1611_end:
__sbr_cell_37_1612:
    lea esi, [r10-1]
__sbr_cell_37_1612_end:
__sbr_cell_37_1613:
    xor edx, edx
__sbr_cell_37_1613_end:
__sbr_cell_37_1614:
    div esi
__sbr_cell_37_1614_end:
__sbr_cell_37_1615:
    mov esi, eax
__sbr_cell_37_1615_end:
__sbr_cell_37_1616:
    add esi, edi
__sbr_cell_37_1616_end:
__sbr_cell_37_1617:
    cmp esi, 24
__sbr_cell_37_1617_end:
__sbr_cell_37_1618:
    ja sbr_reset.L32b9
__sbr_cell_37_1618_end:
__sbr_cell_37_1619:
    mov eax, esi
__sbr_cell_37_1619_end:
__sbr_cell_37_1620:
    movzx eax, WORD PTR [r12+rax*2+311890]
__sbr_cell_37_1620_end:
__sbr_cell_37_1621:
    mov WORD PTR [r12+r8*2+312042], ax
__sbr_cell_37_1621_end:
__sbr_cell_37_1622:
    add r8, 2
__sbr_cell_37_1622_end:
sbr_reset.L2c4a:
__sbr_cell_37_1623:
    add r10d, 4294967294
__sbr_cell_37_1623_end:
__sbr_cell_37_1624:
    cmp r9, r8
__sbr_cell_37_1624_end:
__sbr_cell_37_1625:
    jne sbr_reset.L2bed
__sbr_cell_37_1625_end:
__sbr_cell_37_1626:
    test cl, 1
__sbr_cell_37_1626_end:
__sbr_cell_37_1627:
    je sbr_reset.L2c89
__sbr_cell_37_1627_end:
__sbr_cell_37_1628:
    inc r8
__sbr_cell_37_1628_end:
sbr_reset.L2c5b:
__sbr_cell_37_1629:
    inc ecx
__sbr_cell_37_1629_end:
__sbr_cell_37_1630:
    sub r15d, esi
__sbr_cell_37_1630_end:
__sbr_cell_37_1631:
    sub ecx, r8d
__sbr_cell_37_1631_end:
__sbr_cell_37_1632:
    mov eax, r15d
__sbr_cell_37_1632_end:
__sbr_cell_37_1633:
    xor edx, edx
__sbr_cell_37_1633_end:
__sbr_cell_37_1634:
    div ecx
__sbr_cell_37_1634_end:
__sbr_cell_37_1635:
    add eax, esi
__sbr_cell_37_1635_end:
__sbr_cell_37_1636:
    cmp eax, 24
__sbr_cell_37_1636_end:
__sbr_cell_37_1637:
    ja sbr_reset.L32b9
__sbr_cell_37_1637_end:
__sbr_cell_37_1638:
    mov eax, eax
__sbr_cell_37_1638_end:
__sbr_cell_37_1639:
    movzx eax, WORD PTR [r12+rax*2+311890]
__sbr_cell_37_1639_end:
__sbr_cell_37_1640:
    mov WORD PTR [r12+r8*2+312038], ax
__sbr_cell_37_1640_end:
sbr_reset.L2c89:
__sbr_cell_37_1641:
    mov ecx, DWORD PTR [r12+0]
__sbr_cell_37_1641_end:
__sbr_cell_37_1642:
    mov esi, DWORD PTR [r12+64]
__sbr_cell_37_1642_end:
__sbr_cell_37_1643:
    mov eax, ecx
__sbr_cell_37_1643_end:
__sbr_cell_37_1644:
    sar eax, 1
__sbr_cell_37_1644_end:
__sbr_cell_37_1645:
    add eax, 2048000
__sbr_cell_37_1645_end:
__sbr_cell_37_1646:
    cdq
__sbr_cell_37_1646_end:
__sbr_cell_37_1647:
    idiv ecx
__sbr_cell_37_1647_end:
__sbr_cell_37_1648:
    lea rcx, [r12+311792]
__sbr_cell_37_1648_end:
__sbr_cell_37_1649:
    mov QWORD PTR [rbp-72], rcx
__sbr_cell_37_1649_end:
__sbr_cell_37_1650:
    mov DWORD PTR [r12+312112], 0
__sbr_cell_37_1650_end:
__sbr_cell_37_1651:
    mov edi, r11d
__sbr_cell_37_1651_end:
__sbr_cell_37_1652:
    cmp eax, DWORD PTR [rbp-80]
__sbr_cell_37_1652_end:
__sbr_cell_37_1653:
    jae sbr_reset.L30df
__sbr_cell_37_1653_end:
sbr_reset.L2cc2:
__sbr_cell_37_1654:
    lea rcx, [r12+311792]
__sbr_cell_37_1654_end:
__sbr_cell_37_1655:
    movzx ecx, WORD PTR [rcx+0]
__sbr_cell_37_1655_end:
__sbr_cell_37_1656:
    xor edi, edi
__sbr_cell_37_1656_end:
__sbr_cell_37_1657:
    cmp eax, ecx
__sbr_cell_37_1657_end:
__sbr_cell_37_1658:
    jle sbr_reset.L30df
__sbr_cell_37_1658_end:
__sbr_cell_37_1659:
    movzx ecx, WORD PTR [r12+311794]
__sbr_cell_37_1659_end:
__sbr_cell_37_1660:
    mov edi, 1
__sbr_cell_37_1660_end:
__sbr_cell_37_1661:
    cmp eax, ecx
__sbr_cell_37_1661_end:
__sbr_cell_37_1662:
    jbe sbr_reset.L30df
__sbr_cell_37_1662_end:
__sbr_cell_37_1663:
    movzx ecx, WORD PTR [r12+311796]
__sbr_cell_37_1663_end:
__sbr_cell_37_1664:
    mov edi, 2
__sbr_cell_37_1664_end:
__sbr_cell_37_1665:
    cmp eax, ecx
__sbr_cell_37_1665_end:
__sbr_cell_37_1666:
    jbe sbr_reset.L30df
__sbr_cell_37_1666_end:
sbr_reset.L2d03:
__sbr_cell_37_1667:
    movzx ecx, WORD PTR [r12+311798]
__sbr_cell_37_1667_end:
__sbr_cell_37_1668:
    mov edi, 3
__sbr_cell_37_1668_end:
__sbr_cell_37_1669:
    cmp eax, ecx
__sbr_cell_37_1669_end:
__sbr_cell_37_1670:
    jbe sbr_reset.L30df
__sbr_cell_37_1670_end:
__sbr_cell_37_1671:
    movzx ecx, WORD PTR [r12+311800]
__sbr_cell_37_1671_end:
__sbr_cell_37_1672:
    mov edi, 4
__sbr_cell_37_1672_end:
__sbr_cell_37_1673:
    cmp eax, ecx
__sbr_cell_37_1673_end:
__sbr_cell_37_1674:
    jbe sbr_reset.L30df
__sbr_cell_37_1674_end:
__sbr_cell_37_1675:
    movzx ecx, WORD PTR [r12+311802]
__sbr_cell_37_1675_end:
__sbr_cell_37_1676:
    mov edi, 5
__sbr_cell_37_1676_end:
__sbr_cell_37_1677:
    cmp eax, ecx
__sbr_cell_37_1677_end:
__sbr_cell_37_1678:
    jbe sbr_reset.L30df
__sbr_cell_37_1678_end:
sbr_reset.L2d45:
__sbr_cell_37_1679:
    movzx ecx, WORD PTR [r12+311804]
__sbr_cell_37_1679_end:
__sbr_cell_37_1680:
    mov edi, 6
__sbr_cell_37_1680_end:
__sbr_cell_37_1681:
    cmp eax, ecx
__sbr_cell_37_1681_end:
__sbr_cell_37_1682:
    jbe sbr_reset.L30df
__sbr_cell_37_1682_end:
__sbr_cell_37_1683:
    movzx ecx, WORD PTR [r12+311806]
__sbr_cell_37_1683_end:
__sbr_cell_37_1684:
    mov edi, 7
__sbr_cell_37_1684_end:
__sbr_cell_37_1685:
    cmp eax, ecx
__sbr_cell_37_1685_end:
__sbr_cell_37_1686:
    jbe sbr_reset.L30df
__sbr_cell_37_1686_end:
__sbr_cell_37_1687:
    movzx ecx, WORD PTR [r12+311808]
__sbr_cell_37_1687_end:
__sbr_cell_37_1688:
    mov edi, 8
__sbr_cell_37_1688_end:
__sbr_cell_37_1689:
    cmp eax, ecx
__sbr_cell_37_1689_end:
__sbr_cell_37_1690:
    jbe sbr_reset.L30df
__sbr_cell_37_1690_end:
sbr_reset.L2d87:
__sbr_cell_37_1691:
    movzx ecx, WORD PTR [r12+311810]
__sbr_cell_37_1691_end:
__sbr_cell_37_1692:
    mov edi, 9
__sbr_cell_37_1692_end:
__sbr_cell_37_1693:
    cmp eax, ecx
__sbr_cell_37_1693_end:
__sbr_cell_37_1694:
    jbe sbr_reset.L30df
__sbr_cell_37_1694_end:
__sbr_cell_37_1695:
    movzx ecx, WORD PTR [r12+311812]
__sbr_cell_37_1695_end:
__sbr_cell_37_1696:
    mov edi, 10
__sbr_cell_37_1696_end:
__sbr_cell_37_1697:
    cmp eax, ecx
__sbr_cell_37_1697_end:
__sbr_cell_37_1698:
    jbe sbr_reset.L30df
__sbr_cell_37_1698_end:
__sbr_cell_37_1699:
    movzx ecx, WORD PTR [r12+311814]
__sbr_cell_37_1699_end:
__sbr_cell_37_1700:
    mov edi, 11
__sbr_cell_37_1700_end:
__sbr_cell_37_1701:
    cmp eax, ecx
__sbr_cell_37_1701_end:
__sbr_cell_37_1702:
    jbe sbr_reset.L30df
__sbr_cell_37_1702_end:
sbr_reset.L2dc9:
__sbr_cell_37_1703:
    movzx ecx, WORD PTR [r12+311816]
__sbr_cell_37_1703_end:
__sbr_cell_37_1704:
    mov edi, 12
__sbr_cell_37_1704_end:
__sbr_cell_37_1705:
    cmp eax, ecx
__sbr_cell_37_1705_end:
__sbr_cell_37_1706:
    jbe sbr_reset.L30df
__sbr_cell_37_1706_end:
__sbr_cell_37_1707:
    movzx ecx, WORD PTR [r12+311818]
__sbr_cell_37_1707_end:
__sbr_cell_37_1708:
    mov edi, 13
__sbr_cell_37_1708_end:
__sbr_cell_37_1709:
    cmp eax, ecx
__sbr_cell_37_1709_end:
__sbr_cell_37_1710:
    jbe sbr_reset.L30df
__sbr_cell_37_1710_end:
__sbr_cell_37_1711:
    movzx ecx, WORD PTR [r12+311820]
__sbr_cell_37_1711_end:
__sbr_cell_37_1712:
    mov edi, 14
__sbr_cell_37_1712_end:
__sbr_cell_37_1713:
    cmp eax, ecx
__sbr_cell_37_1713_end:
__sbr_cell_37_1714:
    jbe sbr_reset.L30df
__sbr_cell_37_1714_end:
sbr_reset.L2e0b:
__sbr_cell_37_1715:
    movzx ecx, WORD PTR [r12+311822]
__sbr_cell_37_1715_end:
__sbr_cell_37_1716:
    mov edi, 15
__sbr_cell_37_1716_end:
__sbr_cell_37_1717:
    cmp eax, ecx
__sbr_cell_37_1717_end:
__sbr_cell_37_1718:
    jbe sbr_reset.L30df
__sbr_cell_37_1718_end:
__sbr_cell_37_1719:
    movzx ecx, WORD PTR [r12+311824]
__sbr_cell_37_1719_end:
__sbr_cell_37_1720:
    mov edi, 16
__sbr_cell_37_1720_end:
__sbr_cell_37_1721:
    cmp eax, ecx
__sbr_cell_37_1721_end:
__sbr_cell_37_1722:
    jbe sbr_reset.L30df
__sbr_cell_37_1722_end:
__sbr_cell_37_1723:
    movzx ecx, WORD PTR [r12+311826]
__sbr_cell_37_1723_end:
__sbr_cell_37_1724:
    mov edi, 17
__sbr_cell_37_1724_end:
__sbr_cell_37_1725:
    cmp eax, ecx
__sbr_cell_37_1725_end:
__sbr_cell_37_1726:
    jbe sbr_reset.L30df
__sbr_cell_37_1726_end:
sbr_reset.L2e4d:
__sbr_cell_37_1727:
    movzx ecx, WORD PTR [r12+311828]
__sbr_cell_37_1727_end:
__sbr_cell_37_1728:
    mov edi, 18
__sbr_cell_37_1728_end:
__sbr_cell_37_1729:
    cmp eax, ecx
__sbr_cell_37_1729_end:
__sbr_cell_37_1730:
    jbe sbr_reset.L30df
__sbr_cell_37_1730_end:
__sbr_cell_37_1731:
    movzx ecx, WORD PTR [r12+311830]
__sbr_cell_37_1731_end:
__sbr_cell_37_1732:
    mov edi, 19
__sbr_cell_37_1732_end:
__sbr_cell_37_1733:
    cmp eax, ecx
__sbr_cell_37_1733_end:
__sbr_cell_37_1734:
    jbe sbr_reset.L30df
__sbr_cell_37_1734_end:
__sbr_cell_37_1735:
    movzx ecx, WORD PTR [r12+311832]
__sbr_cell_37_1735_end:
__sbr_cell_37_1736:
    mov edi, 20
__sbr_cell_37_1736_end:
__sbr_cell_37_1737:
    cmp eax, ecx
__sbr_cell_37_1737_end:
__sbr_cell_37_1738:
    jbe sbr_reset.L30df
__sbr_cell_37_1738_end:
sbr_reset.L2e8f:
__sbr_cell_37_1739:
    movzx ecx, WORD PTR [r12+311834]
__sbr_cell_37_1739_end:
__sbr_cell_37_1740:
    mov edi, 21
__sbr_cell_37_1740_end:
__sbr_cell_37_1741:
    cmp eax, ecx
__sbr_cell_37_1741_end:
__sbr_cell_37_1742:
    jbe sbr_reset.L30df
__sbr_cell_37_1742_end:
__sbr_cell_37_1743:
    movzx ecx, WORD PTR [r12+311836]
__sbr_cell_37_1743_end:
__sbr_cell_37_1744:
    mov edi, 22
__sbr_cell_37_1744_end:
__sbr_cell_37_1745:
    cmp eax, ecx
__sbr_cell_37_1745_end:
__sbr_cell_37_1746:
    jbe sbr_reset.L30df
__sbr_cell_37_1746_end:
__sbr_cell_37_1747:
    movzx ecx, WORD PTR [r12+311838]
__sbr_cell_37_1747_end:
__sbr_cell_37_1748:
    mov edi, 23
__sbr_cell_37_1748_end:
__sbr_cell_37_1749:
    cmp eax, ecx
__sbr_cell_37_1749_end:
__sbr_cell_37_1750:
    jbe sbr_reset.L30df
__sbr_cell_37_1750_end:
sbr_reset.L2ed1:
__sbr_cell_37_1751:
    movzx ecx, WORD PTR [r12+311840]
__sbr_cell_37_1751_end:
__sbr_cell_37_1752:
    mov edi, 24
__sbr_cell_37_1752_end:
__sbr_cell_37_1753:
    cmp eax, ecx
__sbr_cell_37_1753_end:
__sbr_cell_37_1754:
    jbe sbr_reset.L30df
__sbr_cell_37_1754_end:
__sbr_cell_37_1755:
    movzx ecx, WORD PTR [r12+311842]
__sbr_cell_37_1755_end:
__sbr_cell_37_1756:
    mov edi, 25
__sbr_cell_37_1756_end:
__sbr_cell_37_1757:
    cmp eax, ecx
__sbr_cell_37_1757_end:
__sbr_cell_37_1758:
    jbe sbr_reset.L30df
__sbr_cell_37_1758_end:
__sbr_cell_37_1759:
    movzx ecx, WORD PTR [r12+311844]
__sbr_cell_37_1759_end:
__sbr_cell_37_1760:
    mov edi, 26
__sbr_cell_37_1760_end:
__sbr_cell_37_1761:
    cmp eax, ecx
__sbr_cell_37_1761_end:
__sbr_cell_37_1762:
    jbe sbr_reset.L30df
__sbr_cell_37_1762_end:
sbr_reset.L2f13:
__sbr_cell_37_1763:
    movzx ecx, WORD PTR [r12+311846]
__sbr_cell_37_1763_end:
__sbr_cell_37_1764:
    mov edi, 27
__sbr_cell_37_1764_end:
__sbr_cell_37_1765:
    cmp eax, ecx
__sbr_cell_37_1765_end:
__sbr_cell_37_1766:
    jbe sbr_reset.L30df
__sbr_cell_37_1766_end:
__sbr_cell_37_1767:
    movzx ecx, WORD PTR [r12+311848]
__sbr_cell_37_1767_end:
__sbr_cell_37_1768:
    mov edi, 28
__sbr_cell_37_1768_end:
__sbr_cell_37_1769:
    cmp eax, ecx
__sbr_cell_37_1769_end:
__sbr_cell_37_1770:
    jbe sbr_reset.L30df
__sbr_cell_37_1770_end:
__sbr_cell_37_1771:
    movzx ecx, WORD PTR [r12+311850]
__sbr_cell_37_1771_end:
__sbr_cell_37_1772:
    mov edi, 29
__sbr_cell_37_1772_end:
__sbr_cell_37_1773:
    cmp eax, ecx
__sbr_cell_37_1773_end:
__sbr_cell_37_1774:
    jbe sbr_reset.L30df
__sbr_cell_37_1774_end:
sbr_reset.L2f55:
__sbr_cell_37_1775:
    movzx ecx, WORD PTR [r12+311852]
__sbr_cell_37_1775_end:
__sbr_cell_37_1776:
    mov edi, 30
__sbr_cell_37_1776_end:
__sbr_cell_37_1777:
    cmp eax, ecx
__sbr_cell_37_1777_end:
__sbr_cell_37_1778:
    jbe sbr_reset.L30df
__sbr_cell_37_1778_end:
__sbr_cell_37_1779:
    movzx ecx, WORD PTR [r12+311854]
__sbr_cell_37_1779_end:
__sbr_cell_37_1780:
    mov edi, 31
__sbr_cell_37_1780_end:
__sbr_cell_37_1781:
    cmp eax, ecx
__sbr_cell_37_1781_end:
__sbr_cell_37_1782:
    jbe sbr_reset.L30df
__sbr_cell_37_1782_end:
__sbr_cell_37_1783:
    movzx ecx, WORD PTR [r12+311856]
__sbr_cell_37_1783_end:
__sbr_cell_37_1784:
    mov edi, 32
__sbr_cell_37_1784_end:
__sbr_cell_37_1785:
    cmp eax, ecx
__sbr_cell_37_1785_end:
__sbr_cell_37_1786:
    jbe sbr_reset.L30df
__sbr_cell_37_1786_end:
sbr_reset.L2f97:
__sbr_cell_37_1787:
    movzx ecx, WORD PTR [r12+311858]
__sbr_cell_37_1787_end:
__sbr_cell_37_1788:
    mov edi, 33
__sbr_cell_37_1788_end:
__sbr_cell_37_1789:
    cmp eax, ecx
__sbr_cell_37_1789_end:
__sbr_cell_37_1790:
    jbe sbr_reset.L30df
__sbr_cell_37_1790_end:
__sbr_cell_37_1791:
    movzx ecx, WORD PTR [r12+311860]
__sbr_cell_37_1791_end:
__sbr_cell_37_1792:
    mov edi, 34
__sbr_cell_37_1792_end:
__sbr_cell_37_1793:
    cmp eax, ecx
__sbr_cell_37_1793_end:
__sbr_cell_37_1794:
    jbe sbr_reset.L30df
__sbr_cell_37_1794_end:
__sbr_cell_37_1795:
    movzx ecx, WORD PTR [r12+311862]
__sbr_cell_37_1795_end:
__sbr_cell_37_1796:
    mov edi, 35
__sbr_cell_37_1796_end:
__sbr_cell_37_1797:
    cmp eax, ecx
__sbr_cell_37_1797_end:
__sbr_cell_37_1798:
    jbe sbr_reset.L30df
__sbr_cell_37_1798_end:
sbr_reset.L2fd9:
__sbr_cell_37_1799:
    movzx ecx, WORD PTR [r12+311864]
__sbr_cell_37_1799_end:
__sbr_cell_37_1800:
    mov edi, 36
__sbr_cell_37_1800_end:
__sbr_cell_37_1801:
    cmp eax, ecx
__sbr_cell_37_1801_end:
__sbr_cell_37_1802:
    jbe sbr_reset.L30df
__sbr_cell_37_1802_end:
__sbr_cell_37_1803:
    movzx ecx, WORD PTR [r12+311866]
__sbr_cell_37_1803_end:
__sbr_cell_37_1804:
    mov edi, 37
__sbr_cell_37_1804_end:
__sbr_cell_37_1805:
    cmp eax, ecx
__sbr_cell_37_1805_end:
__sbr_cell_37_1806:
    jbe sbr_reset.L30df
__sbr_cell_37_1806_end:
__sbr_cell_37_1807:
    movzx ecx, WORD PTR [r12+311868]
__sbr_cell_37_1807_end:
__sbr_cell_37_1808:
    mov edi, 38
__sbr_cell_37_1808_end:
__sbr_cell_37_1809:
    cmp eax, ecx
__sbr_cell_37_1809_end:
__sbr_cell_37_1810:
    jbe sbr_reset.L30df
__sbr_cell_37_1810_end:
sbr_reset.L301b:
__sbr_cell_37_1811:
    movzx ecx, WORD PTR [r12+311870]
__sbr_cell_37_1811_end:
__sbr_cell_37_1812:
    mov edi, 39
__sbr_cell_37_1812_end:
__sbr_cell_37_1813:
    cmp eax, ecx
__sbr_cell_37_1813_end:
__sbr_cell_37_1814:
    jbe sbr_reset.L30df
__sbr_cell_37_1814_end:
__sbr_cell_37_1815:
    movzx ecx, WORD PTR [r12+311872]
__sbr_cell_37_1815_end:
__sbr_cell_37_1816:
    mov edi, 40
__sbr_cell_37_1816_end:
__sbr_cell_37_1817:
    cmp eax, ecx
__sbr_cell_37_1817_end:
__sbr_cell_37_1818:
    jbe sbr_reset.L30df
__sbr_cell_37_1818_end:
__sbr_cell_37_1819:
    movzx ecx, WORD PTR [r12+311874]
__sbr_cell_37_1819_end:
__sbr_cell_37_1820:
    mov edi, 41
__sbr_cell_37_1820_end:
__sbr_cell_37_1821:
    cmp eax, ecx
__sbr_cell_37_1821_end:
__sbr_cell_37_1822:
    jbe sbr_reset.L30df
__sbr_cell_37_1822_end:
sbr_reset.L305d:
__sbr_cell_37_1823:
    movzx ecx, WORD PTR [r12+311876]
__sbr_cell_37_1823_end:
__sbr_cell_37_1824:
    mov edi, 42
__sbr_cell_37_1824_end:
__sbr_cell_37_1825:
    cmp eax, ecx
__sbr_cell_37_1825_end:
__sbr_cell_37_1826:
    jbe sbr_reset.L30df
__sbr_cell_37_1826_end:
__sbr_cell_37_1827:
    movzx ecx, WORD PTR [r12+311878]
__sbr_cell_37_1827_end:
__sbr_cell_37_1828:
    mov edi, 43
__sbr_cell_37_1828_end:
__sbr_cell_37_1829:
    cmp eax, ecx
__sbr_cell_37_1829_end:
__sbr_cell_37_1830:
    jbe sbr_reset.L30df
__sbr_cell_37_1830_end:
__sbr_cell_37_1831:
    movzx ecx, WORD PTR [r12+311880]
__sbr_cell_37_1831_end:
__sbr_cell_37_1832:
    mov edi, 44
__sbr_cell_37_1832_end:
__sbr_cell_37_1833:
    cmp eax, ecx
__sbr_cell_37_1833_end:
__sbr_cell_37_1834:
    jbe sbr_reset.L30df
__sbr_cell_37_1834_end:
sbr_reset.L3093:
__sbr_cell_37_1835:
    movzx ecx, WORD PTR [r12+311882]
__sbr_cell_37_1835_end:
__sbr_cell_37_1836:
    mov edi, 45
__sbr_cell_37_1836_end:
__sbr_cell_37_1837:
    cmp eax, ecx
__sbr_cell_37_1837_end:
__sbr_cell_37_1838:
    jbe sbr_reset.L30df
__sbr_cell_37_1838_end:
__sbr_cell_37_1839:
    movzx ecx, WORD PTR [r12+311884]
__sbr_cell_37_1839_end:
__sbr_cell_37_1840:
    mov edi, 46
__sbr_cell_37_1840_end:
__sbr_cell_37_1841:
    cmp eax, ecx
__sbr_cell_37_1841_end:
__sbr_cell_37_1842:
    jbe sbr_reset.L30df
__sbr_cell_37_1842_end:
__sbr_cell_37_1843:
    movzx ecx, WORD PTR [r12+311886]
__sbr_cell_37_1843_end:
__sbr_cell_37_1844:
    mov edi, 47
__sbr_cell_37_1844_end:
__sbr_cell_37_1845:
    cmp eax, ecx
__sbr_cell_37_1845_end:
__sbr_cell_37_1846:
    jbe sbr_reset.L30df
__sbr_cell_37_1846_end:
sbr_reset.L30c9:
__sbr_cell_37_1847:
    movzx ecx, WORD PTR [r12+311888]
__sbr_cell_37_1847_end:
__sbr_cell_37_1848:
    mov edi, 48
__sbr_cell_37_1848_end:
__sbr_cell_37_1849:
    cmp eax, ecx
__sbr_cell_37_1849_end:
__sbr_cell_37_1850:
    ja sbr_reset.L32dc
__sbr_cell_37_1850_end:
sbr_reset.L30df:
__sbr_cell_37_1851:
    mov eax, 4294967295
__sbr_cell_37_1851_end:
__sbr_cell_37_1852:
    xor r8d, r8d
__sbr_cell_37_1852_end:
__sbr_cell_37_1853:
    xor ecx, ecx
__sbr_cell_37_1853_end:
__sbr_cell_37_1854:
    mov r15d, 4294967295
__sbr_cell_37_1854_end:
__sbr_cell_37_1855:
    mov r9d, esi
__sbr_cell_37_1855_end:
__sbr_cell_37_1856:
    mov r10d, DWORD PTR [rbp-128]
__sbr_cell_37_1856_end:
__sbr_cell_37_1857:
    jmp sbr_reset.L312e
__sbr_cell_37_1857_end:
sbr_reset.L30f8:
__sbr_cell_37_1858:
    inc ecx
__sbr_cell_37_1858_end:
__sbr_cell_37_1859:
    mov DWORD PTR [r12+312112], ecx
__sbr_cell_37_1859_end:
__sbr_cell_37_1860:
    mov r14d, r11d
__sbr_cell_37_1860_end:
__sbr_cell_37_1861:
    mov r10d, r11d
__sbr_cell_37_1861_end:
sbr_reset.L3108:
__sbr_cell_37_1862:
    mov rdx, QWORD PTR [rbp-56]
__sbr_cell_37_1862_end:
__sbr_cell_37_1863:
    mov rbx, QWORD PTR [rbp-72]
__sbr_cell_37_1863_end:
__sbr_cell_37_1864:
    movzx ebx, WORD PTR [rbx+rdi*2+0]
__sbr_cell_37_1864_end:
__sbr_cell_37_1865:
    sub ebx, r11d
__sbr_cell_37_1865_end:
__sbr_cell_37_1866:
    cmp ebx, 3
__sbr_cell_37_1866_end:
__sbr_cell_37_1867:
    cmovl edi, edx
__sbr_cell_37_1867_end:
__sbr_cell_37_1868:
    mov r15d, r9d
__sbr_cell_37_1868_end:
__sbr_cell_37_1869:
    mov r9d, r14d
__sbr_cell_37_1869_end:
__sbr_cell_37_1870:
    cmp WORD PTR [rbp-80], r11w
__sbr_cell_37_1870_end:
__sbr_cell_37_1871:
    je sbr_reset.L320e
__sbr_cell_37_1871_end:
sbr_reset.L312e:
__sbr_cell_37_1872:
    mov r11d, eax
__sbr_cell_37_1872_end:
__sbr_cell_37_1873:
    mov eax, edi
__sbr_cell_37_1873_end:
__sbr_cell_37_1874:
    cmp edi, r11d
__sbr_cell_37_1874_end:
__sbr_cell_37_1875:
    jne sbr_reset.L3141
__sbr_cell_37_1875_end:
__sbr_cell_37_1876:
    cmp r9d, r15d
__sbr_cell_37_1876_end:
__sbr_cell_37_1877:
    je sbr_reset.L31d5
__sbr_cell_37_1877_end:
sbr_reset.L3141:
__sbr_cell_37_1878:
    mov edi, eax
__sbr_cell_37_1878_end:
__sbr_cell_37_1879:
    cmp edi, 48
__sbr_cell_37_1879_end:
__sbr_cell_37_1880:
    ja sbr_reset.L326b
__sbr_cell_37_1880_end:
__sbr_cell_37_1881:
    lea r14d, [r9+rsi*1+0]
__sbr_cell_37_1881_end:
__sbr_cell_37_1882:
    mov rdx, QWORD PTR [rbp-72]
__sbr_cell_37_1882_end:
__sbr_cell_37_1883:
    lea r15, [rdx+rdi*2+0]
__sbr_cell_37_1883_end:
__sbr_cell_37_1884:
    xor r12d, r12d
__sbr_cell_37_1884_end:
__sbr_cell_37_1885:
    .nops 1
__sbr_cell_37_1885_end:
sbr_reset.L3160:
__sbr_cell_37_1886:
    movzx r11d, WORD PTR [r15+r12*2+0]
__sbr_cell_37_1886_end:
__sbr_cell_37_1887:
    lea r13d, [rsi+r11*1+0]
__sbr_cell_37_1887_end:
__sbr_cell_37_1888:
    and r13d, 1
__sbr_cell_37_1888_end:
__sbr_cell_37_1889:
    mov ebx, r13d
__sbr_cell_37_1889_end:
__sbr_cell_37_1890:
    not ebx
__sbr_cell_37_1890_end:
__sbr_cell_37_1891:
    add ebx, r14d
__sbr_cell_37_1891_end:
__sbr_cell_37_1892:
    cmp ebx, r11d
__sbr_cell_37_1892_end:
__sbr_cell_37_1893:
    jae sbr_reset.L318c
__sbr_cell_37_1893_end:
__sbr_cell_37_1894:
    dec r12
__sbr_cell_37_1894_end:
__sbr_cell_37_1895:
    lea r11d, [rdi+r12*1+0]
__sbr_cell_37_1895_end:
__sbr_cell_37_1896:
    cmp r11d, 49
__sbr_cell_37_1896_end:
__sbr_cell_37_1897:
    jb sbr_reset.L3160
__sbr_cell_37_1897_end:
sbr_reset.L3187:
__sbr_cell_37_1898:
    jmp sbr_reset.L326b
__sbr_cell_37_1898_end:
sbr_reset.L318c:
__sbr_cell_37_1899:
    cmp ecx, 6
__sbr_cell_37_1899_end:
__sbr_cell_37_1900:
    jae sbr_reset.L31f5
__sbr_cell_37_1900_end:
__sbr_cell_37_1901:
    mov ebx, ecx
__sbr_cell_37_1901_end:
__sbr_cell_37_1902:
    mov r14d, r11d
__sbr_cell_37_1902_end:
__sbr_cell_37_1903:
    sub r14d, r10d
__sbr_cell_37_1903_end:
__sbr_cell_37_1904:
    test r14d, r14d
__sbr_cell_37_1904_end:
__sbr_cell_37_1905:
    cmovle r14d, r8d
__sbr_cell_37_1905_end:
__sbr_cell_37_1906:
    mov rdx, QWORD PTR [rbp-48]
__sbr_cell_37_1906_end:
__sbr_cell_37_1907:
    mov BYTE PTR [rdx+rbx*1+312116], r14b
__sbr_cell_37_1907_end:
__sbr_cell_37_1908:
    mov r15d, r14d
__sbr_cell_37_1908_end:
__sbr_cell_37_1909:
    add r15d, r13d
__sbr_cell_37_1909_end:
__sbr_cell_37_1910:
    mov r12d, esi
__sbr_cell_37_1910_end:
sbr_reset.L31b5:
__sbr_cell_37_1911:
    sub r12d, r15d
__sbr_cell_37_1911_end:
__sbr_cell_37_1912:
    mov BYTE PTR [rdx+rbx*1+312122], r12b
__sbr_cell_37_1912_end:
__sbr_cell_37_1913:
    mov r12, rdx
__sbr_cell_37_1913_end:
__sbr_cell_37_1914:
    test r14b, r14b
__sbr_cell_37_1914_end:
__sbr_cell_37_1915:
    jne sbr_reset.L30f8
__sbr_cell_37_1915_end:
__sbr_cell_37_1916:
    mov r14d, DWORD PTR [rbp-128]
__sbr_cell_37_1916_end:
__sbr_cell_37_1917:
    jmp sbr_reset.L3108
__sbr_cell_37_1917_end:
sbr_reset.L31d5:
__sbr_cell_37_1918:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_1918_end:
__sbr_cell_37_1919:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_1919_end:
__sbr_cell_37_1920:
    lea rdx, [rip+L_str_19]
__sbr_cell_37_1920_end:
__sbr_cell_37_1921:
    mov esi, 16
__sbr_cell_37_1921_end:
__sbr_cell_37_1922:
    xor eax, eax
__sbr_cell_37_1922_end:
sbr_reset.L31eb:
__sbr_cell_37_1923:
    call av_log
__sbr_cell_37_1923_end:
sbr_reset.L31f0:
__sbr_cell_37_1924:
    jmp sbr_reset.L1d31
__sbr_cell_37_1924_end:
sbr_reset.L31f5:
__sbr_cell_37_1925:
    mov r15, QWORD PTR [rbp-64]
__sbr_cell_37_1925_end:
__sbr_cell_37_1926:
    mov rdi, QWORD PTR [r15+8]
__sbr_cell_37_1926_end:
__sbr_cell_37_1927:
    lea rdx, [rip+L_str_20]
__sbr_cell_37_1927_end:
__sbr_cell_37_1928:
    mov esi, 16
__sbr_cell_37_1928_end:
__sbr_cell_37_1929:
    jmp sbr_reset.L20c8
__sbr_cell_37_1929_end:
sbr_reset.L320e:
__sbr_cell_37_1930:
    cmp ecx, 2
__sbr_cell_37_1930_end:
__sbr_cell_37_1931:
    jb sbr_reset.L3228
__sbr_cell_37_1931_end:
__sbr_cell_37_1932:
    dec ecx
__sbr_cell_37_1932_end:
__sbr_cell_37_1933:
    cmp BYTE PTR [r12+rcx*1+312116], 2
__sbr_cell_37_1933_end:
__sbr_cell_37_1934:
    ja sbr_reset.L3228
__sbr_cell_37_1934_end:
__sbr_cell_37_1935:
    mov DWORD PTR [r12+312112], ecx
__sbr_cell_37_1935_end:
sbr_reset.L3228:
__sbr_cell_37_1936:
    mov rdi, r12
__sbr_cell_37_1936_end:
__sbr_cell_37_1937:
    call sbr_make_f_tablelim
__sbr_cell_37_1937_end:
sbr_reset.L3230:
__sbr_cell_37_1938:
    mov DWORD PTR [r12+88876], 0
__sbr_cell_37_1938_end:
__sbr_cell_37_1939:
    mov DWORD PTR [r12+177644], 0
__sbr_cell_37_1939_end:
__sbr_cell_37_1940:
    jmp sbr_reset.L1d95
__sbr_cell_37_1940_end:
sbr_reset.L324d:
__sbr_cell_37_1941:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1941_end:
sbr_reset.L3252:
__sbr_cell_37_1942:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1942_end:
sbr_reset.L3257:
__sbr_cell_37_1943:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1943_end:
sbr_reset.L325c:
__sbr_cell_37_1944:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1944_end:
sbr_reset.L3261:
__sbr_cell_37_1945:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1945_end:
sbr_reset.L3266:
__sbr_cell_37_1946:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1946_end:
sbr_reset.L326b:
__sbr_cell_37_1947:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1947_end:
sbr_reset.L3270:
__sbr_cell_37_1948:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1948_end:
sbr_reset.L3275:
__sbr_cell_37_1949:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1949_end:
sbr_reset.L327a:
__sbr_cell_37_1950:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1950_end:
sbr_reset.L327f:
__sbr_cell_37_1951:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1951_end:
sbr_reset.L3284:
__sbr_cell_37_1952:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1952_end:
sbr_reset.L3289:
__sbr_cell_37_1953:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1953_end:
sbr_reset.L328e:
__sbr_cell_37_1954:
    lea rdx, [rip+L_str_3]
__sbr_cell_37_1954_end:
__sbr_cell_37_1955:
    lea rcx, [rip+L_str_9]
__sbr_cell_37_1955_end:
__sbr_cell_37_1956:
    lea r8, [rip+L_str_5]
__sbr_cell_37_1956_end:
__sbr_cell_37_1957:
    xor edi, edi
__sbr_cell_37_1957_end:
__sbr_cell_37_1958:
    xor esi, esi
__sbr_cell_37_1958_end:
__sbr_cell_37_1959:
    mov r9d, 345
__sbr_cell_37_1959_end:
__sbr_cell_37_1960:
    xor eax, eax
__sbr_cell_37_1960_end:
sbr_reset.L32af:
__sbr_cell_37_1961:
    call av_log
__sbr_cell_37_1961_end:
sbr_reset.L32b4:
__sbr_cell_37_1962:
    call abort
__sbr_cell_37_1962_end:
sbr_reset.L32b9:
__sbr_cell_37_1963:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1963_end:
sbr_reset.L32be:
__sbr_cell_37_1964:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1964_end:
sbr_reset.L32c3:
__sbr_cell_37_1965:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1965_end:
sbr_reset.L32c8:
__sbr_cell_37_1966:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1966_end:
sbr_reset.L32cd:
__sbr_cell_37_1967:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1967_end:
sbr_reset.L32d2:
__sbr_cell_37_1968:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1968_end:
sbr_reset.L32d7:
__sbr_cell_37_1969:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1969_end:
sbr_reset.L32dc:
__sbr_cell_37_1970:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_37_1970_end:
__sbr_cell_37_1971:
    int3
__sbr_cell_37_1971_end:
__sbr_cell_37_1972:
    int3
__sbr_cell_37_1972_end:
__sbr_cell_37_1973:
    int3
__sbr_cell_37_1973_end:
__sbr_cell_37_1974:
    int3
__sbr_cell_37_1974_end:
__sbr_cell_37_1975:
    int3
__sbr_cell_37_1975_end:
__sbr_cell_37_1976:
    int3
__sbr_cell_37_1976_end:
__sbr_cell_37_1977:
    int3
__sbr_cell_37_1977_end:
__sbr_cell_37_1978:
    int3
__sbr_cell_37_1978_end:
__sbr_cell_37_1979:
    int3
__sbr_cell_37_1979_end:
__sbr_cell_37_1980:
    int3
__sbr_cell_37_1980_end:
__sbr_cell_37_1981:
    int3
__sbr_cell_37_1981_end:
sbr_reset.L32ec:
__sbr_cell_37_1982:
    int3
__sbr_cell_37_1982_end:
__sbr_cell_37_1983:
    int3
__sbr_cell_37_1983_end:
__sbr_cell_37_1984:
    int3
__sbr_cell_37_1984_end:
__sbr_cell_37_1985:
    int3
__sbr_cell_37_1985_end:
.size sbr_reset, .-sbr_reset
.section .text.sbr_x_gen,"ax",@progbits
.globl sbr_x_gen
.type sbr_x_gen,@function
sbr_x_gen:
__sbr_cell_38_0:
    push rbp
__sbr_cell_38_0_end:
__sbr_cell_38_1:
    mov rbp, rsp
__sbr_cell_38_1_end:
__sbr_cell_38_2:
    push r15
__sbr_cell_38_2_end:
__sbr_cell_38_3:
    push r14
__sbr_cell_38_3_end:
__sbr_cell_38_4:
    push r13
__sbr_cell_38_4_end:
__sbr_cell_38_5:
    push r12
__sbr_cell_38_5_end:
__sbr_cell_38_6:
    push rbx
__sbr_cell_38_6_end:
__sbr_cell_38_7:
    sub rsp, 40
__sbr_cell_38_7_end:
__sbr_cell_38_8:
    mov QWORD PTR [rbp-56], rcx
__sbr_cell_38_8_end:
__sbr_cell_38_9:
    cmp r9d, 2
__sbr_cell_38_9_end:
__sbr_cell_38_10:
    jae sbr_x_gen.Lbef3
__sbr_cell_38_10_end:
sbr_x_gen.e1:
__sbr_cell_38_11:
    mov r12, r8
__sbr_cell_38_11_end:
__sbr_cell_38_12:
    mov r13, rdx
__sbr_cell_38_12_end:
__sbr_cell_38_13:
    mov rbx, rdi
__sbr_cell_38_13_end:
__sbr_cell_38_14:
    mov eax, r9d
__sbr_cell_38_14_end:
__sbr_cell_38_15:
    imul rax, rax, 88768
__sbr_cell_38_15_end:
__sbr_cell_38_16:
    movzx eax, BYTE PTR [rdi+rax*1+88869]
__sbr_cell_38_16_end:
__sbr_cell_38_17:
    xor r15d, r15d
__sbr_cell_38_17_end:
__sbr_cell_38_18:
    cmp eax, 17
__sbr_cell_38_18_end:
__sbr_cell_38_19:
    lea r14d, [rax+rax*1-32]
__sbr_cell_38_19_end:
__sbr_cell_38_20:
    cmovb r14d, r15d
__sbr_cell_38_20_end:
sbr_x_gen.e2:
__sbr_cell_38_21:
    mov edx, 19456
__sbr_cell_38_21_end:
__sbr_cell_38_22:
    mov QWORD PTR [rbp-48], rsi
__sbr_cell_38_22_end:
__sbr_cell_38_23:
    mov rdi, rsi
__sbr_cell_38_23_end:
__sbr_cell_38_24:
    xor esi, esi
__sbr_cell_38_24_end:
__sbr_cell_38_25:
    call memset
__sbr_cell_38_25_end:
sbr_x_gen.m1:
__sbr_cell_38_26:
    mov eax, DWORD PTR [rbx+84]
__sbr_cell_38_26_end:
__sbr_cell_38_27:
    mov esi, 0
__sbr_cell_38_27_end:
__sbr_cell_38_28:
    test eax, eax
__sbr_cell_38_28_end:
__sbr_cell_38_29:
    je sbr_x_gen.Lb9cc
__sbr_cell_38_29_end:
__sbr_cell_38_30:
    mov r15d, eax
__sbr_cell_38_30_end:
__sbr_cell_38_31:
    mov esi, eax
__sbr_cell_38_31_end:
__sbr_cell_38_32:
    test r14d, r14d
__sbr_cell_38_32_end:
__sbr_cell_38_33:
    jle sbr_x_gen.Lb9cc
__sbr_cell_38_33_end:
sbr_x_gen.a0:
__sbr_cell_38_34:
    mov eax, r14d
__sbr_cell_38_34_end:
__sbr_cell_38_35:
    shl rax, 8
__sbr_cell_38_35_end:
__sbr_cell_38_36:
    mov rcx, QWORD PTR [rbp-48]
__sbr_cell_38_36_end:
__sbr_cell_38_37:
    add rcx, 10240
__sbr_cell_38_37_end:
__sbr_cell_38_38:
    lea rdx, [r12+36]
__sbr_cell_38_38_end:
__sbr_cell_38_39:
    lea rdi, [rax-512]
__sbr_cell_38_39_end:
__sbr_cell_38_40:
    lea r8, [rax-256]
__sbr_cell_38_40_end:
__sbr_cell_38_41:
    xor esi, esi
__sbr_cell_38_41_end:
__sbr_cell_38_42:
    .nops 1
__sbr_cell_38_42_end:
sbr_x_gen.Lb910:
__sbr_cell_38_43:
    mov r9, rdx
__sbr_cell_38_43_end:
__sbr_cell_38_44:
    xor r10d, r10d
__sbr_cell_38_44_end:
__sbr_cell_38_45:
    .nops 1
__sbr_cell_38_45_end:
sbr_x_gen.Lb920:
__sbr_cell_38_46:
    vmovss xmm0, DWORD PTR [r9-20]
__sbr_cell_38_46_end:
__sbr_cell_38_47:
    vmovss DWORD PTR [rcx+r10*1-10240], xmm0
__sbr_cell_38_47_end:
__sbr_cell_38_48:
    vmovss xmm0, DWORD PTR [r9-16]
__sbr_cell_38_48_end:
__sbr_cell_38_49:
    vmovss DWORD PTR [rcx+r10*1-512], xmm0
__sbr_cell_38_49_end:
__sbr_cell_38_50:
    cmp r8, r10
__sbr_cell_38_50_end:
__sbr_cell_38_51:
    je sbr_x_gen.Lb9a6
__sbr_cell_38_51_end:
sbr_x_gen.a2:
__sbr_cell_38_52:
    vmovss xmm0, DWORD PTR [r9-12]
__sbr_cell_38_52_end:
__sbr_cell_38_53:
    vmovss DWORD PTR [rcx+r10*1-9984], xmm0
__sbr_cell_38_53_end:
__sbr_cell_38_54:
    vmovss xmm0, DWORD PTR [r9-8]
__sbr_cell_38_54_end:
__sbr_cell_38_55:
    vmovss DWORD PTR [rcx+r10*1-256], xmm0
__sbr_cell_38_55_end:
__sbr_cell_38_56:
    cmp rdi, r10
__sbr_cell_38_56_end:
__sbr_cell_38_57:
    je sbr_x_gen.Lb9a6
__sbr_cell_38_57_end:
__sbr_cell_38_58:
    cmp r10, 9216
__sbr_cell_38_58_end:
__sbr_cell_38_59:
    je sbr_x_gen.Lbee9
__sbr_cell_38_59_end:
sbr_x_gen.a3:
__sbr_cell_38_60:
    vmovss xmm0, DWORD PTR [r9-4]
__sbr_cell_38_60_end:
__sbr_cell_38_61:
    vmovss DWORD PTR [rcx+r10*1-9728], xmm0
__sbr_cell_38_61_end:
__sbr_cell_38_62:
    vmovss xmm0, DWORD PTR [r9+0]
__sbr_cell_38_62_end:
__sbr_cell_38_63:
    vmovss DWORD PTR [rcx+r10*1+0], xmm0
__sbr_cell_38_63_end:
__sbr_cell_38_64:
    add r10, 768
__sbr_cell_38_64_end:
__sbr_cell_38_65:
    add r9, 24
__sbr_cell_38_65_end:
__sbr_cell_38_66:
    cmp rax, r10
__sbr_cell_38_66_end:
__sbr_cell_38_67:
    jne sbr_x_gen.Lb920
__sbr_cell_38_67_end:
sbr_x_gen.Lb9a6:
__sbr_cell_38_68:
    inc rsi
__sbr_cell_38_68_end:
__sbr_cell_38_69:
    mov r15d, DWORD PTR [rbx+84]
__sbr_cell_38_69_end:
__sbr_cell_38_70:
    cmp rsi, r15
__sbr_cell_38_70_end:
__sbr_cell_38_71:
    jae sbr_x_gen.Lb9cc
__sbr_cell_38_71_end:
__sbr_cell_38_72:
    add rcx, 4
__sbr_cell_38_72_end:
__sbr_cell_38_73:
    add rdx, 320
__sbr_cell_38_73_end:
__sbr_cell_38_74:
    cmp rsi, 64
__sbr_cell_38_74_end:
__sbr_cell_38_75:
    jne sbr_x_gen.Lb910
__sbr_cell_38_75_end:
sbr_x_gen.t1:
__sbr_cell_38_76:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_76_end:
sbr_x_gen.Lb9cc:
__sbr_cell_38_77:
    add r15d, DWORD PTR [rbx+92]
__sbr_cell_38_77_end:
__sbr_cell_38_78:
    cmp esi, r15d
__sbr_cell_38_78_end:
__sbr_cell_38_79:
    jae sbr_x_gen.Lbba9
__sbr_cell_38_79_end:
__sbr_cell_38_80:
    test r14d, r14d
__sbr_cell_38_80_end:
__sbr_cell_38_81:
    jle sbr_x_gen.Lbba9
__sbr_cell_38_81_end:
__sbr_cell_38_82:
    lea ecx, [r14-1]
__sbr_cell_38_82_end:
__sbr_cell_38_83:
    cmp ecx, 38
__sbr_cell_38_83_end:
__sbr_cell_38_84:
    mov eax, 38
__sbr_cell_38_84_end:
__sbr_cell_38_85:
    cmovb eax, ecx
__sbr_cell_38_85_end:
__sbr_cell_38_86:
    cmp esi, 65
__sbr_cell_38_86_end:
__sbr_cell_38_87:
    mov ecx, 64
__sbr_cell_38_87_end:
__sbr_cell_38_88:
    cmovae ecx, esi
__sbr_cell_38_88_end:
__sbr_cell_38_89:
    cmp esi, 63
__sbr_cell_38_89_end:
__sbr_cell_38_90:
    ja sbr_x_gen.Lbba4
__sbr_cell_38_90_end:
sbr_x_gen.b0:
__sbr_cell_38_91:
    mov edi, r14d
__sbr_cell_38_91_end:
__sbr_cell_38_92:
    mov esi, esi
__sbr_cell_38_92_end:
__sbr_cell_38_93:
    mov QWORD PTR [rbp-72], rdi
__sbr_cell_38_93_end:
__sbr_cell_38_94:
    and edi, 2147483644
__sbr_cell_38_94_end:
__sbr_cell_38_95:
    lea rdx, [rsi*4+0]
__sbr_cell_38_95_end:
__sbr_cell_38_96:
    mov QWORD PTR [rbp-64], rdx
__sbr_cell_38_96_end:
__sbr_cell_38_97:
    mov rdx, QWORD PTR [rbp-48]
__sbr_cell_38_97_end:
__sbr_cell_38_98:
    lea r9, [rdx+10496]
__sbr_cell_38_98_end:
__sbr_cell_38_99:
    lea r10, [rdx+rsi*4+0]
__sbr_cell_38_99_end:
__sbr_cell_38_100:
    lea r11, [rsi*8+16384]
__sbr_cell_38_100_end:
__sbr_cell_38_101:
    add r11, r13
__sbr_cell_38_101_end:
__sbr_cell_38_102:
    add r13, 17924
__sbr_cell_38_102_end:
__sbr_cell_38_103:
    .nops 1
__sbr_cell_38_103_end:
sbr_x_gen.Lba50:
__sbr_cell_38_104:
    cmp eax, 38
__sbr_cell_38_104_end:
__sbr_cell_38_105:
    je sbr_x_gen.Lbeee
__sbr_cell_38_105_end:
__sbr_cell_38_106:
    cmp r14d, 4
__sbr_cell_38_106_end:
__sbr_cell_38_107:
    jae sbr_x_gen.Lba70
__sbr_cell_38_107_end:
__sbr_cell_38_108:
    xor r15d, r15d
__sbr_cell_38_108_end:
__sbr_cell_38_109:
    jmp sbr_x_gen.Lbb30
__sbr_cell_38_109_end:
__sbr_cell_38_110:
    .nops 1
__sbr_cell_38_110_end:
sbr_x_gen.Lba70:
__sbr_cell_38_111:
    mov r8, QWORD PTR [rbp-64]
__sbr_cell_38_111_end:
__sbr_cell_38_112:
    xor r15d, r15d
__sbr_cell_38_112_end:
__sbr_cell_38_113:
    .nops 1
__sbr_cell_38_113_end:
sbr_x_gen.Lba80:
__sbr_cell_38_114:
    vmovss xmm0, DWORD PTR [r13+r8*2-1540]
__sbr_cell_38_114_end:
__sbr_cell_38_115:
    vmovss DWORD PTR [r9+r8*1-10496], xmm0
__sbr_cell_38_115_end:
__sbr_cell_38_116:
    vmovss xmm0, DWORD PTR [r13+r8*2-1536]
__sbr_cell_38_116_end:
__sbr_cell_38_117:
    vmovss DWORD PTR [r9+r8*1-768], xmm0
__sbr_cell_38_117_end:
__sbr_cell_38_118:
    vmovss xmm0, DWORD PTR [r13+r8*2-1028]
__sbr_cell_38_118_end:
__sbr_cell_38_119:
    vmovss DWORD PTR [r9+r8*1-10240], xmm0
__sbr_cell_38_119_end:
__sbr_cell_38_120:
    vmovss xmm0, DWORD PTR [r13+r8*2-1024]
__sbr_cell_38_120_end:
__sbr_cell_38_121:
    vmovss DWORD PTR [r9+r8*1-512], xmm0
__sbr_cell_38_121_end:
sbr_x_gen.b2:
__sbr_cell_38_122:
    vmovss xmm0, DWORD PTR [r13+r8*2-516]
__sbr_cell_38_122_end:
__sbr_cell_38_123:
    vmovss DWORD PTR [r9+r8*1-9984], xmm0
__sbr_cell_38_123_end:
__sbr_cell_38_124:
    vmovss xmm0, DWORD PTR [r13+r8*2-512]
__sbr_cell_38_124_end:
__sbr_cell_38_125:
    vmovss DWORD PTR [r9+r8*1-256], xmm0
__sbr_cell_38_125_end:
__sbr_cell_38_126:
    vmovss xmm0, DWORD PTR [r13+r8*2-4]
__sbr_cell_38_126_end:
__sbr_cell_38_127:
    vmovss DWORD PTR [r9+r8*1-9728], xmm0
__sbr_cell_38_127_end:
__sbr_cell_38_128:
    vmovss xmm0, DWORD PTR [r13+r8*2+0]
__sbr_cell_38_128_end:
__sbr_cell_38_129:
    vmovss DWORD PTR [r9+r8*1+0], xmm0
__sbr_cell_38_129_end:
sbr_x_gen.b3:
__sbr_cell_38_130:
    add r15, 4
__sbr_cell_38_130_end:
__sbr_cell_38_131:
    add r8, 1024
__sbr_cell_38_131_end:
__sbr_cell_38_132:
    cmp rdi, r15
__sbr_cell_38_132_end:
__sbr_cell_38_133:
    jne sbr_x_gen.Lba80
__sbr_cell_38_133_end:
__sbr_cell_38_134:
    test BYTE PTR [rbp-72], 2
__sbr_cell_38_134_end:
__sbr_cell_38_135:
    je sbr_x_gen.Lbb7d
__sbr_cell_38_135_end:
sbr_x_gen.Lbb30:
__sbr_cell_38_136:
    mov r8, r15
__sbr_cell_38_136_end:
__sbr_cell_38_137:
    shl r8, 8
__sbr_cell_38_137_end:
__sbr_cell_38_138:
    add r8, r10
__sbr_cell_38_138_end:
__sbr_cell_38_139:
    shl r15, 9
__sbr_cell_38_139_end:
__sbr_cell_38_140:
    add r15, r11
__sbr_cell_38_140_end:
__sbr_cell_38_141:
    xor edx, edx
__sbr_cell_38_141_end:
__sbr_cell_38_142:
    .nops 1
__sbr_cell_38_142_end:
sbr_x_gen.Lbb50:
__sbr_cell_38_143:
    vmovss xmm0, DWORD PTR [r15+rdx*2+0]
__sbr_cell_38_143_end:
__sbr_cell_38_144:
    vmovss DWORD PTR [r8+rdx*1+0], xmm0
__sbr_cell_38_144_end:
__sbr_cell_38_145:
    vmovss xmm0, DWORD PTR [r15+rdx*2+4]
__sbr_cell_38_145_end:
__sbr_cell_38_146:
    vmovss DWORD PTR [r8+rdx*1+9728], xmm0
__sbr_cell_38_146_end:
__sbr_cell_38_147:
    add rdx, 256
__sbr_cell_38_147_end:
__sbr_cell_38_148:
    cmp rdx, 512
__sbr_cell_38_148_end:
__sbr_cell_38_149:
    jne sbr_x_gen.Lbb50
__sbr_cell_38_149_end:
sbr_x_gen.Lbb7d:
__sbr_cell_38_150:
    inc rsi
__sbr_cell_38_150_end:
__sbr_cell_38_151:
    mov edx, DWORD PTR [rbx+92]
__sbr_cell_38_151_end:
__sbr_cell_38_152:
    add edx, DWORD PTR [rbx+84]
__sbr_cell_38_152_end:
__sbr_cell_38_153:
    cmp rsi, rdx
__sbr_cell_38_153_end:
__sbr_cell_38_154:
    jae sbr_x_gen.Lbba9
__sbr_cell_38_154_end:
__sbr_cell_38_155:
    add r13, 8
__sbr_cell_38_155_end:
__sbr_cell_38_156:
    add r9, 4
__sbr_cell_38_156_end:
__sbr_cell_38_157:
    add r10, 4
__sbr_cell_38_157_end:
__sbr_cell_38_158:
    add r11, 8
__sbr_cell_38_158_end:
__sbr_cell_38_159:
    cmp rsi, rcx
__sbr_cell_38_159_end:
__sbr_cell_38_160:
    jne sbr_x_gen.Lba50
__sbr_cell_38_160_end:
sbr_x_gen.Lbba4:
__sbr_cell_38_161:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_161_end:
sbr_x_gen.Lbba9:
__sbr_cell_38_162:
    mov r11d, DWORD PTR [rbx+88]
__sbr_cell_38_162_end:
__sbr_cell_38_163:
    test r11d, r11d
__sbr_cell_38_163_end:
__sbr_cell_38_164:
    je sbr_x_gen.Lbd11
__sbr_cell_38_164_end:
__sbr_cell_38_165:
    mov eax, r11d
__sbr_cell_38_165_end:
__sbr_cell_38_166:
    cmp r14d, 37
__sbr_cell_38_166_end:
__sbr_cell_38_167:
    jg sbr_x_gen.Lbd16
__sbr_cell_38_167_end:
sbr_x_gen.c0:
__sbr_cell_38_168:
    movsxd rcx, r14d
__sbr_cell_38_168_end:
__sbr_cell_38_169:
    mov edx, 2
__sbr_cell_38_169_end:
__sbr_cell_38_170:
    sub rdx, rcx
__sbr_cell_38_170_end:
__sbr_cell_38_171:
    lea rsi, [rcx-35]
__sbr_cell_38_171_end:
__sbr_cell_38_172:
    mov rax, rcx
__sbr_cell_38_172_end:
__sbr_cell_38_173:
    shl rax, 8
__sbr_cell_38_173_end:
__sbr_cell_38_174:
    mov r10, QWORD PTR [rbp-48]
__sbr_cell_38_174_end:
__sbr_cell_38_175:
    lea rdi, [rax+r10*1+0]
__sbr_cell_38_175_end:
__sbr_cell_38_176:
    add rdi, 9728
__sbr_cell_38_176_end:
__sbr_cell_38_177:
    lea r8, [r12+20]
__sbr_cell_38_177_end:
__sbr_cell_38_178:
    mov r9d, edx
__sbr_cell_38_178_end:
__sbr_cell_38_179:
    shl r9d, 5
__sbr_cell_38_179_end:
__sbr_cell_38_180:
    and r9d, 64
__sbr_cell_38_180_end:
__sbr_cell_38_181:
    xor eax, eax
__sbr_cell_38_181_end:
__sbr_cell_38_182:
    .nops 1
__sbr_cell_38_182_end:
sbr_x_gen.Lbc00:
__sbr_cell_38_183:
    mov r11, rcx
__sbr_cell_38_183_end:
__sbr_cell_38_184:
    test dl, 2
__sbr_cell_38_184_end:
__sbr_cell_38_185:
    je sbr_x_gen.Lbc39
__sbr_cell_38_185_end:
__sbr_cell_38_186:
    xor r15d, r15d
__sbr_cell_38_186_end:
__sbr_cell_38_187:
    mov r11, rcx
__sbr_cell_38_187_end:
__sbr_cell_38_188:
    .nops 1
__sbr_cell_38_188_end:
sbr_x_gen.Lbc10:
__sbr_cell_38_189:
    vmovss xmm0, DWORD PTR [r8+r11*8-4]
__sbr_cell_38_189_end:
__sbr_cell_38_190:
    vmovss DWORD PTR [rdi+r15*8-9728], xmm0
__sbr_cell_38_190_end:
__sbr_cell_38_191:
    vmovss xmm0, DWORD PTR [r8+r11*8+0]
__sbr_cell_38_191_end:
__sbr_cell_38_192:
    vmovss DWORD PTR [rdi+r15*8+0], xmm0
__sbr_cell_38_192_end:
__sbr_cell_38_193:
    inc r11
__sbr_cell_38_193_end:
__sbr_cell_38_194:
    add r15, 32
__sbr_cell_38_194_end:
__sbr_cell_38_195:
    cmp r9, r15
__sbr_cell_38_195_end:
__sbr_cell_38_196:
    jne sbr_x_gen.Lbc10
__sbr_cell_38_196_end:
sbr_x_gen.Lbc39:
__sbr_cell_38_197:
    cmp esi, 3
__sbr_cell_38_197_end:
__sbr_cell_38_198:
    jb sbr_x_gen.Lbce0
__sbr_cell_38_198_end:
__sbr_cell_38_199:
    lea r15, [r11+5]
__sbr_cell_38_199_end:
__sbr_cell_38_200:
    shl r11, 8
__sbr_cell_38_200_end:
__sbr_cell_38_201:
    add r11, r10
__sbr_cell_38_201_end:
__sbr_cell_38_202:
    .nops 1
__sbr_cell_38_202_end:
sbr_x_gen.Lbc50:
__sbr_cell_38_203:
    vmovss xmm0, DWORD PTR [r12+r15*8-24]
__sbr_cell_38_203_end:
__sbr_cell_38_204:
    vmovss DWORD PTR [r11+0], xmm0
__sbr_cell_38_204_end:
__sbr_cell_38_205:
    vmovss xmm0, DWORD PTR [r12+r15*8-20]
__sbr_cell_38_205_end:
__sbr_cell_38_206:
    vmovss DWORD PTR [r11+9728], xmm0
__sbr_cell_38_206_end:
__sbr_cell_38_207:
    vmovss xmm0, DWORD PTR [r12+r15*8-16]
__sbr_cell_38_207_end:
__sbr_cell_38_208:
    vmovss DWORD PTR [r11+256], xmm0
__sbr_cell_38_208_end:
__sbr_cell_38_209:
    vmovss xmm0, DWORD PTR [r12+r15*8-12]
__sbr_cell_38_209_end:
__sbr_cell_38_210:
    vmovss DWORD PTR [r11+9984], xmm0
__sbr_cell_38_210_end:
sbr_x_gen.c2:
__sbr_cell_38_211:
    vmovss xmm0, DWORD PTR [r12+r15*8-8]
__sbr_cell_38_211_end:
__sbr_cell_38_212:
    vmovss DWORD PTR [r11+512], xmm0
__sbr_cell_38_212_end:
__sbr_cell_38_213:
    vmovss xmm0, DWORD PTR [r12+r15*8-4]
__sbr_cell_38_213_end:
__sbr_cell_38_214:
    vmovss DWORD PTR [r11+10240], xmm0
__sbr_cell_38_214_end:
__sbr_cell_38_215:
    vmovss xmm0, DWORD PTR [r12+r15*8+0]
__sbr_cell_38_215_end:
__sbr_cell_38_216:
    vmovss DWORD PTR [r11+768], xmm0
__sbr_cell_38_216_end:
__sbr_cell_38_217:
    vmovss xmm0, DWORD PTR [r12+r15*8+4]
__sbr_cell_38_217_end:
__sbr_cell_38_218:
    vmovss DWORD PTR [r11+10496], xmm0
__sbr_cell_38_218_end:
sbr_x_gen.c3:
__sbr_cell_38_219:
    add r15, 4
__sbr_cell_38_219_end:
__sbr_cell_38_220:
    add r11, 1024
__sbr_cell_38_220_end:
__sbr_cell_38_221:
    cmp r15, 43
__sbr_cell_38_221_end:
__sbr_cell_38_222:
    jne sbr_x_gen.Lbc50
__sbr_cell_38_222_end:
sbr_x_gen.Lbce0:
__sbr_cell_38_223:
    inc rax
__sbr_cell_38_223_end:
__sbr_cell_38_224:
    mov r11d, DWORD PTR [rbx+88]
__sbr_cell_38_224_end:
__sbr_cell_38_225:
    cmp rax, r11
__sbr_cell_38_225_end:
__sbr_cell_38_226:
    jae sbr_x_gen.Lbd16
__sbr_cell_38_226_end:
__sbr_cell_38_227:
    add rdi, 4
__sbr_cell_38_227_end:
__sbr_cell_38_228:
    add r8, 320
__sbr_cell_38_228_end:
__sbr_cell_38_229:
    add r10, 4
__sbr_cell_38_229_end:
__sbr_cell_38_230:
    add r12, 320
__sbr_cell_38_230_end:
__sbr_cell_38_231:
    cmp rax, 64
__sbr_cell_38_231_end:
__sbr_cell_38_232:
    jne sbr_x_gen.Lbc00
__sbr_cell_38_232_end:
sbr_x_gen.t2:
__sbr_cell_38_233:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_233_end:
sbr_x_gen.Lbd11:
__sbr_cell_38_234:
    xor r11d, r11d
__sbr_cell_38_234_end:
__sbr_cell_38_235:
    xor eax, eax
__sbr_cell_38_235_end:
sbr_x_gen.Lbd16:
__sbr_cell_38_236:
    add r11d, DWORD PTR [rbx+96]
__sbr_cell_38_236_end:
__sbr_cell_38_237:
    cmp eax, r11d
__sbr_cell_38_237_end:
__sbr_cell_38_238:
    jae sbr_x_gen.Lbed8
__sbr_cell_38_238_end:
__sbr_cell_38_239:
    cmp r14d, 31
__sbr_cell_38_239_end:
__sbr_cell_38_240:
    jg sbr_x_gen.Lbed8
__sbr_cell_38_240_end:
__sbr_cell_38_241:
    cmp eax, 65
__sbr_cell_38_241_end:
__sbr_cell_38_242:
    mov ecx, 64
__sbr_cell_38_242_end:
__sbr_cell_38_243:
    cmovae ecx, eax
__sbr_cell_38_243_end:
__sbr_cell_38_244:
    cmp eax, 63
__sbr_cell_38_244_end:
__sbr_cell_38_245:
    ja sbr_x_gen.Lbed3
__sbr_cell_38_245_end:
sbr_x_gen.d0:
__sbr_cell_38_246:
    mov edx, r14d
__sbr_cell_38_246_end:
__sbr_cell_38_247:
    mov eax, eax
__sbr_cell_38_247_end:
__sbr_cell_38_248:
    mov esi, r14d
__sbr_cell_38_248_end:
__sbr_cell_38_249:
    neg esi
__sbr_cell_38_249_end:
__sbr_cell_38_250:
    and esi, 2
__sbr_cell_38_250_end:
__sbr_cell_38_251:
    add r14d, 4294967267
__sbr_cell_38_251_end:
__sbr_cell_38_252:
    mov rdi, rdx
__sbr_cell_38_252_end:
__sbr_cell_38_253:
    shl rdi, 8
__sbr_cell_38_253_end:
__sbr_cell_38_254:
    lea rdi, [rdi+rax*4+0]
__sbr_cell_38_254_end:
__sbr_cell_38_255:
    mov r11, QWORD PTR [rbp-48]
__sbr_cell_38_255_end:
__sbr_cell_38_256:
    add rdi, r11
__sbr_cell_38_256_end:
__sbr_cell_38_257:
    add rdi, 9728
__sbr_cell_38_257_end:
sbr_x_gen.d1:
__sbr_cell_38_258:
    mov r8, rdx
__sbr_cell_38_258_end:
__sbr_cell_38_259:
    shl r8, 9
__sbr_cell_38_259_end:
__sbr_cell_38_260:
    mov r15, QWORD PTR [rbp-56]
__sbr_cell_38_260_end:
__sbr_cell_38_261:
    lea r9, [r15+rax*8+0]
__sbr_cell_38_261_end:
__sbr_cell_38_262:
    add r8, r9
__sbr_cell_38_262_end:
__sbr_cell_38_263:
    add r8, 4
__sbr_cell_38_263_end:
__sbr_cell_38_264:
    mov r9d, esi
__sbr_cell_38_264_end:
__sbr_cell_38_265:
    shl r9d, 8
__sbr_cell_38_265_end:
__sbr_cell_38_266:
    lea r10d, [rsi-2]
__sbr_cell_38_266_end:
__sbr_cell_38_267:
    add r10, rdx
__sbr_cell_38_267_end:
__sbr_cell_38_268:
    add r10, 2
__sbr_cell_38_268_end:
__sbr_cell_38_269:
    lea r11, [r11+rax*4+0]
__sbr_cell_38_269_end:
__sbr_cell_38_270:
    lea r15, [r15+rax*8+0]
__sbr_cell_38_270_end:
__sbr_cell_38_271:
    add r15, 1540
__sbr_cell_38_271_end:
__sbr_cell_38_272:
    .nops 1
__sbr_cell_38_272_end:
sbr_x_gen.Lbdb0:
__sbr_cell_38_273:
    mov r12, rdx
__sbr_cell_38_273_end:
__sbr_cell_38_274:
    test esi, esi
__sbr_cell_38_274_end:
__sbr_cell_38_275:
    je sbr_x_gen.Lbdec
__sbr_cell_38_275_end:
__sbr_cell_38_276:
    xor r12d, r12d
__sbr_cell_38_276_end:
__sbr_cell_38_277:
    .nops 1
__sbr_cell_38_277_end:
sbr_x_gen.Lbdc0:
__sbr_cell_38_278:
    vmovss xmm0, DWORD PTR [r8+r12*2-4]
__sbr_cell_38_278_end:
__sbr_cell_38_279:
    vmovss DWORD PTR [rdi+r12*1-9728], xmm0
__sbr_cell_38_279_end:
__sbr_cell_38_280:
    vmovss xmm0, DWORD PTR [r8+r12*2+0]
__sbr_cell_38_280_end:
__sbr_cell_38_281:
    vmovss DWORD PTR [rdi+r12*1+0], xmm0
__sbr_cell_38_281_end:
__sbr_cell_38_282:
    add r12, 256
__sbr_cell_38_282_end:
__sbr_cell_38_283:
    cmp r9d, r12d
__sbr_cell_38_283_end:
__sbr_cell_38_284:
    jne sbr_x_gen.Lbdc0
__sbr_cell_38_284_end:
__sbr_cell_38_285:
    mov r12, r10
__sbr_cell_38_285_end:
sbr_x_gen.Lbdec:
__sbr_cell_38_286:
    cmp r14d, 3
__sbr_cell_38_286_end:
__sbr_cell_38_287:
    jb sbr_x_gen.Lbeaa
__sbr_cell_38_287_end:
__sbr_cell_38_288:
    lea r13d, [r12-1]
__sbr_cell_38_288_end:
__sbr_cell_38_289:
    shl r12, 8
__sbr_cell_38_289_end:
__sbr_cell_38_290:
    .nops 1
__sbr_cell_38_290_end:
sbr_x_gen.Lbe00:
__sbr_cell_38_291:
    vmovss xmm0, DWORD PTR [r15+r12*2-1540]
__sbr_cell_38_291_end:
__sbr_cell_38_292:
    vmovss DWORD PTR [r11+r12*1+0], xmm0
__sbr_cell_38_292_end:
__sbr_cell_38_293:
    vmovss xmm0, DWORD PTR [r15+r12*2-1536]
__sbr_cell_38_293_end:
__sbr_cell_38_294:
    vmovss DWORD PTR [r11+r12*1+9728], xmm0
__sbr_cell_38_294_end:
__sbr_cell_38_295:
    vmovss xmm0, DWORD PTR [r15+r12*2-1028]
__sbr_cell_38_295_end:
__sbr_cell_38_296:
    vmovss DWORD PTR [r11+r12*1+256], xmm0
__sbr_cell_38_296_end:
__sbr_cell_38_297:
    vmovss xmm0, DWORD PTR [r15+r12*2-1024]
__sbr_cell_38_297_end:
__sbr_cell_38_298:
    vmovss DWORD PTR [r11+r12*1+9984], xmm0
__sbr_cell_38_298_end:
sbr_x_gen.d2:
__sbr_cell_38_299:
    vmovss xmm0, DWORD PTR [r15+r12*2-516]
__sbr_cell_38_299_end:
__sbr_cell_38_300:
    vmovss DWORD PTR [r11+r12*1+512], xmm0
__sbr_cell_38_300_end:
__sbr_cell_38_301:
    vmovss xmm0, DWORD PTR [r15+r12*2-512]
__sbr_cell_38_301_end:
__sbr_cell_38_302:
    vmovss DWORD PTR [r11+r12*1+10240], xmm0
__sbr_cell_38_302_end:
__sbr_cell_38_303:
    vmovss xmm0, DWORD PTR [r15+r12*2-4]
__sbr_cell_38_303_end:
__sbr_cell_38_304:
    vmovss DWORD PTR [r11+r12*1+768], xmm0
__sbr_cell_38_304_end:
__sbr_cell_38_305:
    vmovss xmm0, DWORD PTR [r15+r12*2+0]
__sbr_cell_38_305_end:
__sbr_cell_38_306:
    vmovss DWORD PTR [r11+r12*1+10496], xmm0
__sbr_cell_38_306_end:
sbr_x_gen.d3:
__sbr_cell_38_307:
    add r13d, 4
__sbr_cell_38_307_end:
__sbr_cell_38_308:
    add r12, 1024
__sbr_cell_38_308_end:
__sbr_cell_38_309:
    cmp r13d, 31
__sbr_cell_38_309_end:
__sbr_cell_38_310:
    jl sbr_x_gen.Lbe00
__sbr_cell_38_310_end:
sbr_x_gen.Lbeaa:
__sbr_cell_38_311:
    inc rax
__sbr_cell_38_311_end:
__sbr_cell_38_312:
    mov r12d, DWORD PTR [rbx+96]
__sbr_cell_38_312_end:
__sbr_cell_38_313:
    add r12d, DWORD PTR [rbx+88]
__sbr_cell_38_313_end:
__sbr_cell_38_314:
    cmp rax, r12
__sbr_cell_38_314_end:
__sbr_cell_38_315:
    jae sbr_x_gen.Lbed8
__sbr_cell_38_315_end:
__sbr_cell_38_316:
    add rdi, 4
__sbr_cell_38_316_end:
__sbr_cell_38_317:
    add r8, 8
__sbr_cell_38_317_end:
__sbr_cell_38_318:
    add r11, 4
__sbr_cell_38_318_end:
__sbr_cell_38_319:
    add r15, 8
__sbr_cell_38_319_end:
__sbr_cell_38_320:
    cmp rax, rcx
__sbr_cell_38_320_end:
__sbr_cell_38_321:
    jne sbr_x_gen.Lbdb0
__sbr_cell_38_321_end:
sbr_x_gen.Lbed3:
__sbr_cell_38_322:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_322_end:
sbr_x_gen.Lbed8:
__sbr_cell_38_323:
    xor eax, eax
__sbr_cell_38_323_end:
__sbr_cell_38_324:
    add rsp, 40
__sbr_cell_38_324_end:
__sbr_cell_38_325:
    pop rbx
__sbr_cell_38_325_end:
__sbr_cell_38_326:
    pop r12
__sbr_cell_38_326_end:
__sbr_cell_38_327:
    pop r13
__sbr_cell_38_327_end:
__sbr_cell_38_328:
    pop r14
__sbr_cell_38_328_end:
__sbr_cell_38_329:
    pop r15
__sbr_cell_38_329_end:
__sbr_cell_38_330:
    pop rbp
__sbr_cell_38_330_end:
sbr_x_gen.done:
__sbr_cell_38_331:
    ret
__sbr_cell_38_331_end:
sbr_x_gen.Lbee9:
__sbr_cell_38_332:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_332_end:
sbr_x_gen.Lbeee:
__sbr_cell_38_333:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_333_end:
sbr_x_gen.Lbef3:
__sbr_cell_38_334:
    ud1 eax, DWORD PTR [eax+18]
__sbr_cell_38_334_end:
__sbr_cell_38_335:
    int3
__sbr_cell_38_335_end:
__sbr_cell_38_336:
    int3
__sbr_cell_38_336_end:
__sbr_cell_38_337:
    int3
__sbr_cell_38_337_end:
__sbr_cell_38_338:
    int3
__sbr_cell_38_338_end:
__sbr_cell_38_339:
    int3
__sbr_cell_38_339_end:
__sbr_cell_38_340:
    int3
__sbr_cell_38_340_end:
__sbr_cell_38_341:
    int3
__sbr_cell_38_341_end:
__sbr_cell_38_342:
    int3
__sbr_cell_38_342_end:
.size sbr_x_gen, .-sbr_x_gen
.section .note.GNU-stack,"",@progbits

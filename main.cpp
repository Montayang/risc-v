#include <iostream>

using namespace std;
unsigned int reg[32];
unsigned char mem[500000];
unsigned int pc = 0;

int binary_str_to_int(string s) {
    int rst = 0;
    while (!s.empty()) {
        rst += rst + (s[0] - '0');
        s = s.substr(1);
    }
    return rst;
}

int hex_str_to_int(string s) {
    int rst = 0;
    while (!s.empty()) {
        if (s[0] >= '0' && s[0] <= '9') rst += 15 * rst + (s[0] - '0');
        else rst += 15 * rst + (s[0] - 'A' + 10);
        s = s.substr(1);
    }
    return rst;
}

int get(unsigned int tar, int a, int b) {
    //cut out the no_a number to the no_b number of tar
    tar = tar >> b;
    int x = int(1 << (a - b + 1)) - 1;
    return tar & x;
}

int sext(unsigned int cmd, char type) {
    int imm = 0;
    switch (type) {
        case 'I': {
            int x = cmd >> 31;
            for (int i = 0; i < 21; i++) imm = (imm << 1) + x;
            imm = imm << 11;
            imm += get(cmd, 30, 20);
            break;
        }
        case 'S': {
            int x = cmd >> 31;
            for (int i = 0; i < 21; i++) imm = (imm << 1) + x;
            imm = imm << 11;
            imm += get(cmd, 30, 25) << 5;
            imm += get(cmd, 11, 8) << 1;
            imm += get(cmd, 7, 7);
            break;
        }
        case 'B': {
            int x = cmd >> 31;
            for (int i = 0; i < 20; i++) imm = (imm << 1) + x;
            imm = (imm << 1) + get(cmd, 7, 7);
            imm = imm << 11;
            imm += get(cmd, 30, 25) << 5;
            imm += get(cmd, 11, 8) << 1;
            break;
        }
        case 'U': {
            imm = get(cmd, 31, 12);
            imm = imm << 12;
            break;
        }
        case 'J': {
            int x = cmd >> 31;
            for (int i = 0; i < 12; i++) imm = (imm << 1) + x;
            imm = imm << 20;
            imm += get(cmd, 19, 12) << 12;
            imm += get(cmd, 20, 20) << 11;
            imm += get(cmd, 30, 21) << 1;
            break;
        }
        default:
            break;
    }
    return imm;
}

unsigned int sext_(int cmd, int num) {
    int x = cmd >> (num - 1);
    if (x) return cmd & ((1 << 31) - 1 + (1 << 31));
    return cmd;
}

enum instruction {
    LUI,
    AUIPC,
    JAL,
    JALR,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    SB,
    SH,
    SW,
    ADDI,
    SLTI,
    SLTIU,
    XORI,
    ORI,
    ANDI,
    SLLI,
    SRLI,
    SRAI,
    ADD,
    SUB,
    SLL,
    SLT,
    SLTU,
    XOR,
    SRL,
    SRA,
    OR,
    AND
};

struct CMD {
    unsigned int cmd = 0, pc = 0;

    CMD() = default;

    CMD(int _cmd) : cmd(_cmd) {}
};

struct object {
    instruction cmd_type;
    int imm = 0;
    unsigned int rd = 0, x_rs1 = 0, x_rs2 = 0, pc = 0;
    int shamt = 0;

    object() = default;

    object(instruction _cmd_type, int _imm, unsigned int _rd, unsigned int _x_rs1 = 0, unsigned int _x_rs2 = 0,
           int _shamt = 0)
            : cmd_type(_cmd_type), x_rs1(_x_rs1), x_rs2(_x_rs2), rd(_rd), shamt(_shamt), imm(_imm) {}
};

struct MEM_and_WB {
    int MEM_offset;
    int flag;
    int byte_num;
    int imm;
    int WB_reg;

    MEM_and_WB() = default;

    MEM_and_WB(int _MEM_offset, int _flag, int _byte_num, unsigned int _imm, int _WB_reg) : MEM_offset(_MEM_offset),
                                                                                            flag(_flag),
                                                                                            byte_num(_byte_num),
                                                                                            imm(_imm),
                                                                                            WB_reg(_WB_reg) {}
};

struct counter {
    int value;

    void operator++() {
        if (value < 3) value++;
    }

    void operator--() {
        if (value) value--;
    }
} predictor[512][8];
counter &f=predictor[0][0];
int history[512];

int h(unsigned int x) {
    return x % 512;
}

CMD IF_ID;
object ID_EX;
MEM_and_WB EX_MEM;
MEM_and_WB MEM_WB;
bool is_end, ID_oc, EX_oc, MEM_oc, WB_oc;
bool data_hazard_1_1, data_hazard_1_2, data_hazard_2_1, data_hazard_2_2;
int former_rd;
int forecast,f_num=0,c_num=0;

void IF() {
    if (ID_oc) return;
    ID_oc = true;
    IF_ID.cmd = mem[pc] + (mem[pc + 1] << 8) + (mem[pc + 2] << 16) + (mem[pc + 3] << 24);
    IF_ID.pc = pc, pc += 4;
}

void ID() {
    if (!ID_oc || EX_oc) return;
    if (IF_ID.cmd == 0x0ff00513) {
        is_end = true;
        return;
    }
    EX_oc = true, ID_oc = false;
    unsigned int cmd = IF_ID.cmd;
    int opcode = get(cmd, 6, 0);
    switch (opcode) {
        case 0b0110111: {//LUI
            ID_EX = object(LUI, sext(cmd, 'U'), get(cmd, 11, 7));
            ID_EX.pc = IF_ID.pc;
            return;
        }
        case 0b0010111: {//AUIPC
            ID_EX = object(AUIPC, sext(cmd, 'U'), get(cmd, 11, 7));
            ID_EX.pc = IF_ID.pc;
            return;
        }
        case 0b1101111: {//JAL
            ID_EX = object(JAL, sext(cmd, 'J'), get(cmd, 11, 7));
            ID_EX.pc = IF_ID.pc;
            return;
        }
        case 0b1100111: {//JALR
            int rs1 = get(cmd, 19, 15);
            if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
            if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
            ID_EX = object(JALR, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
            ID_EX.pc = IF_ID.pc;
            return;
        }
        case 0b1100011: {//BEQ BNE BLT BGE BLTU BGEU
            int funct3 = get(cmd, 14, 12);
            forecast = 0,f_num++,c_num++;
            switch (funct3) {
                case 0b000: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(BEQ, sext(cmd, 'B'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    f = predictor[h(ID_EX.pc)][history[h(ID_EX.pc)]%8];/**/
                    if (f.value > 1) {
                        ++(history[h(ID_EX.pc)]*=2);
                        ++f;
                        pc = ID_EX.pc + ID_EX.imm;
                        forecast = 1;
                    } else history[h(ID_EX.pc)]*=2,--f;
                    return;
                }
                case 0b001: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(BNE, sext(cmd, 'B'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    f = predictor[h(ID_EX.pc)][history[h(ID_EX.pc)]%8];/**/
                    if (f.value > 1) {
                        ++(history[h(ID_EX.pc)]*=2);
                        ++f;
                        pc = ID_EX.pc + ID_EX.imm;
                        forecast = 1;
                    } else history[h(ID_EX.pc)]*=2,--f;
                    return;
                }
                case 0b100: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(BLT, sext(cmd, 'B'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    f = predictor[h(ID_EX.pc)][history[h(ID_EX.pc)]%8];/**/
                    if (f.value > 1) {
                        ++(history[h(ID_EX.pc)]*=2);
                        ++f;
                        pc = ID_EX.pc + ID_EX.imm;
                        forecast = 1;
                    } else history[h(ID_EX.pc)]*=2,--f;
                    return;
                }
                case 0b101: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(BGE, sext(cmd, 'B'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    f = predictor[h(ID_EX.pc)][history[h(ID_EX.pc)]%8];/**/
                    if (f.value > 1) {
                        ++(history[h(ID_EX.pc)]*=2);
                        ++f;
                        pc = ID_EX.pc + ID_EX.imm;
                        forecast = 1;
                    } else history[h(ID_EX.pc)]*=2,--f;
                    return;
                }
                case 0b110: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(BLTU, sext(cmd, 'B'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    f = predictor[h(ID_EX.pc)][history[h(ID_EX.pc)]%8];/**/
                    if (f.value > 1) {
                        ++(history[h(ID_EX.pc)]*=2);
                        ++f;
                        pc = ID_EX.pc + ID_EX.imm;
                        forecast = 1;
                    } else history[h(ID_EX.pc)]*=2,--f;
                    return;
                }
                case 0b111: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(BGEU, sext(cmd, 'B'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    f = predictor[h(ID_EX.pc)][history[h(ID_EX.pc)]%8];/**/
                    if (f.value > 1) {
                        ++(history[h(ID_EX.pc)]*=2);
                        ++f;
                        pc = ID_EX.pc + ID_EX.imm;
                        forecast = 1;
                    } else history[h(ID_EX.pc)]*=2,--f;
                    return;
                }
                default:
                    break;
            }
        }
        case 0b0000011: {//LB LH LW LBU LHU
            int funct3 = get(cmd, 14, 12);
            switch (funct3) {
                case 0b000: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(LB, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b001: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(LH, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b010: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(LW, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b100: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(LBU, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b101: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(LHU, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                default:
                    break;
            }
        }
        case 0b0100011: {//SB SH SW
            int funct3 = get(cmd, 14, 12);
            switch (funct3) {
                case 0b000: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(SB, sext(cmd, 'S'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b001: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(SH, sext(cmd, 'S'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b010: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(SW, sext(cmd, 'S'), 0, reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                default:
                    break;
            }
        }
        case 0b0010011: {//ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI
            int funct3 = get(cmd, 14, 12);
            switch (funct3) {
                case 0b000: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(ADDI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b010: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(SLTI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b011: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(SLTIU, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b100: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(XORI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b110: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(ORI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b111: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(ANDI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b001: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    ID_EX = object(SLLI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1], 0, get(cmd, 24, 20));
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b101: {
                    int rs1 = get(cmd, 19, 15);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (!get(cmd, 30, 30))
                        ID_EX = object(SRLI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1], 0,
                                       get(cmd, 24, 20));
                    else
                        ID_EX = object(SRAI, sext(cmd, 'I'), get(cmd, 11, 7), reg[rs1], 0,
                                       get(cmd, 24, 20));
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                default:
                    break;
            }
        }
        case 0b0110011: {//ADD SUB SLL SLT SLTU XOR SRL SRA OR AND
            int funct3 = get(cmd, 14, 12);
            switch (funct3) {
                case 0b000: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    if (!get(cmd, 30, 30))
                        ID_EX = object(ADD, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    else ID_EX = object(SUB, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b001: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(SLL, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b010: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(SLT, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b011: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(SLTU, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b100: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(XOR, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b101: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    if (!get(cmd, 30, 30))
                        ID_EX = object(SRL, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    else ID_EX = object(SRA, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b110: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(OR, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                case 0b111: {
                    int rs1 = get(cmd, 19, 15), rs2 = get(cmd, 24, 20);
                    if (rs1 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_1 = true;//
                    if (rs2 == EX_MEM.WB_reg && MEM_oc) data_hazard_1_2 = true;//
                    if (rs1 == MEM_WB.WB_reg && WB_oc) data_hazard_2_1 = true;//
                    if (rs2 == MEM_WB.WB_reg && WB_oc) data_hazard_2_2 = true;//
                    ID_EX = object(AND, 0, get(cmd, 11, 7), reg[rs1], reg[rs2]);
                    ID_EX.pc = IF_ID.pc;
                    return;
                }
                default:
                    break;
            }
        }
        default:
            break;
    }
}

void EX() {
    if (!EX_oc || MEM_oc) return;
    MEM_oc = true, EX_oc = false;
    object ob = ID_EX;
    if (data_hazard_2_1) ob.x_rs1 = reg[former_rd];
    if (data_hazard_2_2) ob.x_rs2 = reg[former_rd];
    if (data_hazard_1_1 && MEM_WB.WB_reg != 0) ob.x_rs1 = MEM_WB.imm;
    if (data_hazard_1_2 && MEM_WB.WB_reg != 0) ob.x_rs2 = MEM_WB.imm;
    data_hazard_1_1 = data_hazard_1_2 = data_hazard_2_1 = data_hazard_2_2 = false;
    int imm = ob.imm, rd = ob.rd;
    unsigned int x_rs1 = ob.x_rs1, x_rs2 = ob.x_rs2, shamt = ob.shamt;
    switch (ob.cmd_type) {
        case LUI: {
            EX_MEM = MEM_and_WB(0, 0, 0, imm, rd);
            break;
        }
        case AUIPC: {
            EX_MEM = MEM_and_WB(0, 0, 0, ID_EX.pc + imm, rd);
            break;
        }
        case JAL: {
            EX_MEM = MEM_and_WB(0, 0, 0, ID_EX.pc + 4, rd);
            ID_oc = false;//
            pc = ID_EX.pc + imm;
            break;
        }
        case JALR: {
            int t = ID_EX.pc + 4;
            pc = (x_rs1 + imm) & ~1;
            ID_oc = false;//
            EX_MEM = MEM_and_WB(0, 0, 0, t, rd);
            break;
        }
        case BEQ: {
            if (x_rs1 != x_rs2 && forecast) {
                history[h(ID_EX.pc)]--;
                --f,--f;
                pc = ID_EX.pc + 4;
                ID_oc = false;
                c_num--;
            }
            if (x_rs1 == x_rs2 && !forecast) {
                history[h(ID_EX.pc)]++;
                ++f,++f;
                pc = ID_EX.pc + imm;
                ID_oc = false;
                c_num--;
            }
            break;
        }
        case BNE: {
            if (x_rs1 == x_rs2 && forecast) {
                history[h(ID_EX.pc)]--;
                --f,--f;
                pc = ID_EX.pc + 4;
                ID_oc = false;
                c_num--;
            }
            if (x_rs1 != x_rs2 && !forecast) {
                history[h(ID_EX.pc)]++;
                ++f,++f;
                pc = ID_EX.pc + imm;
                ID_oc = false;
                c_num--;
            }
            break;
        }
        case BLT: {
            if ((signed int) x_rs1 >= (signed int) x_rs2 && forecast) {
                history[h(ID_EX.pc)]--;
                --f,--f;
                pc = ID_EX.pc + 4;
                ID_oc = false;
                c_num--;
            }
            if ((signed int) x_rs1 < (signed int) x_rs2 && !forecast) {
                history[h(ID_EX.pc)]++;
                ++f,++f;
                pc = ID_EX.pc + imm;
                ID_oc = false;
                c_num--;
            }
            break;
        }
        case BGE: {
            if ((signed int) x_rs1 < (signed int) x_rs2 && forecast) {
                history[h(ID_EX.pc)]--;
                --f,--f;
                pc = ID_EX.pc + 4;
                ID_oc = false;
                c_num--;
            }
            if ((signed int) x_rs1 >= (signed int) x_rs2 && !forecast) {
                history[h(ID_EX.pc)]++;
                ++f,++f;
                pc = ID_EX.pc + imm;
                ID_oc = false;
                c_num--;
            }
            break;
        }
        case BLTU: {
            if ((unsigned int) x_rs1 >= (unsigned int) x_rs2 && forecast) {
                history[h(ID_EX.pc)]--;
                --f,--f;
                pc = ID_EX.pc + 4;
                ID_oc = false;
                c_num--;
            }
            if ((unsigned int) x_rs1 < (unsigned int) x_rs2 && !forecast) {
                history[h(ID_EX.pc)]++;
                ++f,++f;
                pc = ID_EX.pc + imm;
                ID_oc = false;
                c_num--;
            }
            break;
        }
        case BGEU: {
            if ((unsigned int) x_rs1 < (unsigned int) x_rs2 && forecast) {
                history[h(ID_EX.pc)]--;
                --f,--f;
                pc = ID_EX.pc + 4;
                ID_oc = false;
                c_num--;
            }
            if ((unsigned int) x_rs1 >= (unsigned int) x_rs2 && !forecast) {
                history[h(ID_EX.pc)]++;
                ++f,++f;
                pc = ID_EX.pc + imm;
                ID_oc = false;
                c_num--;
            }
            break;
        }
        case LB: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 1, 1, 0, rd);
            break;
        }
        case LH: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 1, 2, 0, rd);
            break;
        }
        case LW: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 1, 4, 0, rd);
            break;
        }
        case LBU: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 2, 1, 0, rd);
            break;
        }
        case LHU: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 2, 2, 0, rd);
            break;
        }
        case SB: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 3, 1, x_rs2, 0);
            break;
        }
        case SH: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 3, 2, x_rs2, 0);
            break;
        }
        case SW: {
            EX_MEM = MEM_and_WB(x_rs1 + imm, 3, 4, x_rs2, 0);
            break;
        }
        case ADDI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 + imm, rd);
            break;
        }
        case SLTI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 < imm, rd);
            break;
        }
        case SLTIU: {
            EX_MEM = MEM_and_WB(0, 0, 0, (unsigned int) x_rs1 < (unsigned int) imm, rd);
            break;
        }
        case XORI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 ^ imm, rd);
            break;
        }
        case ORI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 | imm, rd);
            break;
        }
        case ANDI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 & imm, rd);
            break;
        }
        case SLLI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 << shamt, rd);
            break;
        }
        case SRLI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 >> (unsigned int) shamt, rd);
            break;
        }
        case SRAI: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 >> shamt, rd);
            break;
        }
        case ADD: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 + x_rs2, rd);
            break;
        }
        case SUB: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 - x_rs2, rd);
            break;
        }
        case SLL: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 << x_rs2, rd);
            break;
        }
        case SLT: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 < x_rs2, rd);
            break;
        }
        case SLTU: {
            EX_MEM = MEM_and_WB(0, 0, 0, (unsigned int) x_rs1 < (unsigned int) x_rs2, rd);
            break;
        }
        case XOR: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 ^ x_rs2, rd);
            break;
        }
        case SRL: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 >> (unsigned int) x_rs2, rd);
            break;
        }
        case SRA: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 >> x_rs2, rd);
            break;
        }
        case OR: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 | x_rs2, rd);
            break;
        }
        case AND: {
            EX_MEM = MEM_and_WB(0, 0, 0, x_rs1 & x_rs2, rd);
            break;
        }
        default:
            break;
    }
}

void MEM() {
    if (!MEM_oc || WB_oc) return;
    WB_oc = true, MEM_oc = false;
    MEM_WB = EX_MEM;
    switch (MEM_WB.flag) {
        case 1: {
            for (int i = 0; i < MEM_WB.byte_num; i++) MEM_WB.imm += mem[MEM_WB.MEM_offset + i] << (8 * i);
            MEM_WB.imm = sext_(MEM_WB.imm, MEM_WB.byte_num * 8);
            break;
        }
        case 2: {
            for (int i = 0; i < MEM_WB.byte_num; i++) MEM_WB.imm += mem[MEM_WB.MEM_offset + i] << (8 * i);
            break;
        }
        case 3: {
            for (int i = 0; i < MEM_WB.byte_num; i++) mem[MEM_WB.MEM_offset + i] = get(MEM_WB.imm, i * 8 + 7, i * 8);
            break;
        }
        default:
            break;
    }
}

void WB() {
    if (!WB_oc) return;
    former_rd = MEM_WB.WB_reg;
    WB_oc = false;
    reg[MEM_WB.WB_reg] = MEM_WB.imm;
    reg[0] = 0;
}

int main() {
    string s;
    int mem_offset;
    while (cin >> s) {
        if (s[0] == '*') break;
        if (s[0] == '@') mem_offset = hex_str_to_int(s.substr(1));
        else {
            mem[mem_offset] = hex_str_to_int(s);
            mem_offset++;
        }
    }
    while (!is_end || WB_oc || MEM_oc || EX_oc || ID_oc) {
        if (is_end) {
            WB(), MEM(), EX();
            break;
        }
        WB();
        MEM();
        EX();
        ID();
        IF();
    }
    printf("%u\n", reg[10] & 255u);
    printf("%.2f\n",(double(c_num))*100/f_num);
    return 0;
}
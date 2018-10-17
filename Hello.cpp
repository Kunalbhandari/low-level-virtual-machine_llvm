//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/SSAUpdaterImpl.h"
#include "llvm/CodeGen/MachineSSAUpdater.h"
#include "llvm/Transforms/IPO/PartialInlining.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include <map>
#include <vector>
using namespace llvm;

#define DEBUG_TYPE "hello"

STATISTIC(HelloCounter, "Counts number of functions greeted");

namespace {
// Hello0 - The first implementation, without getAnalysisUsage.
struct Hello0 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  Hello0() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    BasicBlock *B;
    Instruction *I;
    Module *c = F.getParent();
    LLVMContext &tx = c->getContext();
    const SCEV *to;
    int m = 0;
    SmallVector<GetElementPtrInst *, 32> dw;
    SmallVector<StoreInst *, 32> df;
    GetElementPtrInst *we, *wr, *wt;
    StoreInst *wq, *temp;
    const DataLayout &DL = F.getParent()->getDataLayout();
    bool ty;
    for (Function::iterator i = F.begin(); i != F.end(); i++) {
      BasicBlock *B = &*i;
      Loop *ji = LI.getLoopFor(B);
      for (Instruction &a : *B) {
        GetElementPtrInst *fr = dyn_cast<GetElementPtrInst>(&a);
        wt = fr;
        if (fr == NULL)
          continue;
        else {
          const SCEV *sc = SE.getSCEV(fr);
          if (ji != NULL) {
            const SCEV *sf = SE.getSCEVAtScope(sc, ji);
            errs() << "\nscev loop " << *sf << "\n";
            const SCEV *sd = SE.getPointerBase(sf);
            const SCEV *dis = SE.getMinusSCEV(sf, sd);
            errs() << "dispacement :" << *dis << "\n";
          } else {
            errs() << "\n" << *sc << "\n";
            const SCEV *sd = SE.getPointerBase(sc);
            const SCEV *dis = SE.getMinusSCEV(sc, sd);
            errs() << "dispacement :" << *dis;
          }
        }
      }
    }
    m = 0;
    for (Function::iterator i = F.begin(); i != F.end(); i++) {
      Loop *ji = LI.getLoopFor(B);
      BasicBlock *B = &*i;
      for (Instruction &a : *B) {
        GetElementPtrInst *fr = dyn_cast<GetElementPtrInst>(&a);
        if (fr == NULL)
          continue;
        else {
          if (ji != NULL) {
            Instruction *xg = a.getNextNode();
            StoreInst *gx = dyn_cast<StoreInst>(xg);
            if (m == 1 && gx != NULL) {
              ty = llvm::isConsecutiveAccess(wq, gx, DL, SE);
              if (ty == false) {
                m = 2;
              } else
                wq = gx;
            }
            if (m == 0 && gx != NULL) {
              m = 1;
              wq = gx;
            }
          } else {
            Instruction *xg = a.getNextNode();
            StoreInst *gx = dyn_cast<StoreInst>(xg);
            if (m == 1 && gx != NULL) {
              ty = llvm::isConsecutiveAccess(wq, gx, DL, SE);
              if (ty == false) {
                m = 2;
              } else
                wq = gx;
            }
            if (m == 0 && gx != NULL) {
              m = 1;
              wq = gx;
            }
          }
        }
      }
    }
    if (ty == false)
      errs() << "\n not consecutive accesses\n\n";
    else {
      errs() << "\n consecutive accesses\n\n";
      exit(0);
    }
    int n, j;
    GetElementPtrInst *pb;
    SmallVector<StoreInst *, 32>::iterator z;
    for (Function::iterator i = F.begin(); i != F.end(); i++) {
      BasicBlock *B = &*i;
      Loop *ji = LI.getLoopFor(B);
      for (Instruction &a : *B) {
        GetElementPtrInst *fo = dyn_cast<GetElementPtrInst>(&a);
        if (fo == NULL)
          continue;
        else {
          Instruction *xg = a.getNextNode();
          StoreInst *gx = dyn_cast<StoreInst>(xg);
          df.push_back(gx);
        }
      }
      for (Instruction &a : *B) {
        GetElementPtrInst *fo = dyn_cast<GetElementPtrInst>(&a);
        if (fo == NULL)
          continue;
        else {
          dw.push_back(fo);
        }
      }
      for (n = 0; n < df.size(); n++) {
        for (j = 0; j < df.size() - n - 1; j++) {
          if (llvm::isConsecutiveAccess(df[j], df[j + 1], DL, SE) == false) {
            temp = df[j];
            df[j] = df[j + 1];
            df[j + 1] = temp;
            pb = dw[j];
            dw[j] = dw[j + 1];
            dw[j + 1] = pb;
          }
        }
      }
      for (z = df.begin(); z != df.end(); z++) {
        errs() << **z << "\n";
      }
      errs() << "\n";
      for (GetElementPtrInst *tv : dw) {
        errs() << *tv << "\n";
      }
      errs() << "\n";
      for (BasicBlock::iterator t = B->begin(); t != B->end(); t++) {
        Instruction *Ii = &*t;
        Loop *ji = LI.getLoopFor(B);
        int j = 0, pos = 0;
        StoreInst *Ss = dyn_cast<StoreInst>(Ii);
        if (Ss != NULL) {
          for (int i = 0; i < df.size(); i++)
            if (df[i] == Ii)
              pos = i;
          for (int i = 0; i < pos; i++) {
            df[i]->moveBefore(df[pos]);
            dw[i]->moveBefore(dw[pos]);
          }
          for (int j = df.size() - 1; j > pos; j--) {
            df[j]->moveAfter(df[pos]);
            dw[j]->moveAfter(dw[pos]);
          }
          if (ji != NULL) {
            for (StoreInst *tit : df) {
              for (Use &pq : tit->operands()) {
                Value *kj = pq.get();
                Instruction *lh = dyn_cast<Instruction>(kj);
                lh->moveBefore(tit);
              }
            }
          }
        }
      }
      df.clear();
      dw.clear();
    }
    errs() << "\n\n" << *c << "\n\n";
  }
  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    //  AU.addRequiredTransitive<AAResultsWrapperPass>();
    AU.addRequiredTransitive<ScalarEvolutionWrapperPass>();
    AU.addRequiredTransitive<LoopInfoWrapperPass>();
  }
};
}
char Hello0::ID = 0;
static RegisterPass<Hello0> J("hello0", "Hello World Pass");

namespace {
// Hello2 - The second implementation with getAnalysisUsage implemented.
struct Hello2 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  Hello2() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    int block = 0, inst, min = 1, max = 1;
    for (Function::iterator i = F.begin(); i != F.end();) {
      BasicBlock *b = &*i++;
      block++;
      inst = 0;
      errs() << "block name " << b->getName() << " ";
      for (Instruction &g : *b) {
        inst++;
      }
      errs() << "instructions: " << inst << "\n";
      if (inst > max) {
        max = inst;
      }
      if (inst < min) {
        min = inst;
      }
    }
    errs() << "block with maximum instructions is: " << max << "\n";
    errs() << "block with minimum instructions is : " << min << "\n";
  }
  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }
};
}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");

namespace {
// Hello3 - The first implementation, without getAnalysisUsage.
struct Hello3 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  Hello3() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    int count;
    for (Function::iterator i = F.begin(); i != F.end();) {
      BasicBlock *b = &*i++;
      errs() << "predecessors of basic block: " << b->getName();
      count = 0;
      for (BasicBlock *pred : predecessors(b)) {
        errs() << "\n" << pred->getName();
        count++;
      }
      errs() << "\n" << count << "\n\n";
      count = 0;
      errs() << "successors of basic block: " << b->getName();
      for (BasicBlock *pred : successors(b)) {
        errs() << "\n " << pred->getName();
        count++;
      }
      errs() << "\n" << count << "\n\n";
    }
  }
};
}

char Hello3::ID = 0;
static RegisterPass<Hello3> Z("hello3", "Hello3 World Pass");

namespace {
// Hello1 - The first implementation, without getAnalysisUsage.
struct Hello4 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  Hello4() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if (F.getName() == "cttError") {
      return false;
    }
    int count = -1, pcount = 0, a, acount;
    std::map<BasicBlock *, int> m;
    std::map<BasicBlock *, int> d;
    std::map<BasicBlock *, int> D;
    std::map<BasicBlock *, int> G;
    SmallVector<BasicBlock *, 32> BB;
    Module *c = F.getParent();
    LLVMContext &tx = c->getContext();
    Constant *dd = c->getOrInsertGlobal("DD", Type::getInt32Ty(tx));
    for (Function::iterator i = F.begin(); i != F.end();) {
      BasicBlock *b = &*i++;
      m[b] = ++count;
      BB.push_back(b);
    }
    for (Function::iterator i = F.begin(); i != F.end();) {
      BasicBlock *b = &*i++;
      BasicBlock *tr;
      for (BasicBlock *pred : predecessors(b)) {
        ++pcount;
        tr = pred;
      }
      if (pcount == 0) {
        d[b] = m[b];
      } else if (pcount == 1) {
        d[b] = m[b] ^ m[tr];
      } else {
        d[b] = m[b] ^ m[tr];
        a = m[tr];
        for (BasicBlock *pred : predecessors(b)) {
          D[pred] = m[pred] ^ a;
          Instruction *yu = b->getFirstNonPHI();
          IRBuilder<> bs(yu);
          bs.CreateStore(bs.getInt32(D[pred]), dd);
        }
      }
      pcount = 0;
    }
    Constant *gg = c->getOrInsertGlobal("GG", Type::getInt32Ty(tx));
    const Twine &Name = "error_ctt";
    BasicBlock *bh, *bi;
    acount = pcount = 0;

    for (BasicBlock *b : BB) {
      Instruction *yu = b->getFirstNonPHI();
      IRBuilder<> bs(yu);
      for (BasicBlock *pred : predecessors(b)) {
        ++pcount;
      }
      if (pcount == 0) {
        bs.CreateStore(bs.getInt32(d[b]), gg);
        bh = b->Create(tx, Name, b->getParent());
        IRBuilder<> bf(bh);
        Constant *fu = c->getFunction("cttError");
        bf.CreateCall(fu);
        bf.CreateRet(bf.getInt32(0));
      }
      if (pcount == 1) {
        LoadInst *hj = bs.CreateLoad(gg);
        Value *ou = bs.CreateXor(hj, bs.getInt32(d[b]));
        bs.CreateStore(ou, gg);
        Value *ut = bs.CreateICmpEQ(ou, bs.getInt32(m[b]));
        Instruction *trr = dyn_cast<Instruction>(ut);
        bi = b->splitBasicBlock(trr->getNextNode());
        Instruction *sa = b->getTerminator();
        sa->eraseFromParent();
        bs.SetInsertPoint(b);
        BranchInst *se = bs.CreateCondBr(ut, bi, bh);
      }
      if (pcount > 1) {
        LoadInst *hj = bs.CreateLoad(gg);
        Value *ou = bs.CreateXor(hj, bs.getInt32(d[b]));
        LoadInst *op = bs.CreateLoad(dd);
        Value *om = bs.CreateXor(ou, op);
        bs.CreateStore(om, gg);
        Value *ut = bs.CreateICmpEQ(om, bs.getInt32(m[b]));
        Instruction *trr = dyn_cast<Instruction>(ut);
        bi = b->splitBasicBlock(trr->getNextNode());
        Instruction *sa = b->getTerminator();
        sa->eraseFromParent();
        bs.SetInsertPoint(b);
        BranchInst *se = bs.CreateCondBr(ut, bi, bh);
      }
      pcount = 0;
    }
    errs() << *c << "\n";
  }
};
}

char Hello4::ID = 0;
static RegisterPass<Hello4> N("hello4", "Hello World Pass");

namespace {
// Hello1 - The second implementation with getAnalysisUsage implemented.
struct Hello1 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  Hello1() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if (F.getName() != "func") {
      return false;
    }
    int m = 0;
    Value *uq;
    Module *c = F.getParent();
    Instruction *ld, *la, *ls, *yu;
    BasicBlock *iy, *ie, *iw, *iwi;
    LLVMContext &tx = c->getContext();
    auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    ArrayRef<BasicBlock *> block;
    PHINode *PN;
    Value *ds;
    GetElementPtrInst *kun;
    LoadInst *acp;
    Instruction *pj;
    for (Loop *l : LI) {
      assert(l->getLoopLatch() && "no loop latch ");
      assert(l->getHeader() && "no loop header");
      assert(l->getExitingBlock() && "no exit block");
      iy = l->getHeader();
      iw = l->getExitingBlock();
      block = l->getBlocks();
      iwi = l->getLoopLatch();
      for (m = 0; m < block.size(); m++)
        if (block[m] != l->getHeader() && block[m] != l->getLoopLatch())
          ie = block[m];
      Instruction *iu;
      if (iy != NULL) {
        la = iy->getFirstNonPHI();
        ls = la->getNextNode();
        Instruction *yu = iy->getTerminator();
        iu = iy->getFirstNonPHI();
        IRBuilder<> bs(yu);
        Instruction *inst;
        for (m = 0; m < block.size(); m++)
          if (block[m] != l->getHeader() && block[m] != l->getLoopLatch())
            inst = block[m]->getFirstNonPHI();
        Value *bq = bs.CreateSub(iu, bs.getInt32(1));
        uq = bs.CreateGEP(inst, bq);
        acp = bs.CreateLoad(uq);
      }

      if (ie != NULL) {
        ld = ie->getFirstNonPHI();
        ld->moveBefore(iu);
        Instruction *yu = ie->getFirstNonPHI();
        IRBuilder<> bs(yu);
        PN = bs.CreatePHI(Type::getInt32Ty(tx), 2, "five");
        PN->addIncoming(acp, iy);
        for (Instruction &a : *ie) {
          GetElementPtrInst *gm = dyn_cast<GetElementPtrInst>(&a);
          if (gm != NULL) {
            Instruction *cgf = gm;
            Instruction *cq = gm->getNextNode();
            del(cq);
            cq->eraseFromParent();
            cgf->eraseFromParent();
            Instruction *iop = ie->getFirstNonPHI();
            del(iop);
            iop->eraseFromParent();
            break;
          }
        }
        for (Instruction &a : *ie) {
          GetElementPtrInst *gm = dyn_cast<GetElementPtrInst>(&a);
          if (gm != NULL) {
            kun = gm;
          }
        }
        Instruction *oops = ie->getTerminator();
        IRBuilder<> bf(oops);
        ds = bf.CreateAdd(PN, bf.getInt32(2));
        StoreInst *st = bf.CreateStore(ds, kun);
      }
      if (iwi != NULL) {
        yu = iwi->getTerminator();
        IRBuilder<> bs(yu);
        Instruction *loas = la->clone();
        Instruction *load = ls->clone();
        loas->insertBefore(yu);
        load->insertBefore(yu);
        Value *rx = bs.CreateICmpSLT(loas, load);
        yu = iwi->getTerminator();
        yu->eraseFromParent();
        bs.SetInsertPoint(iwi);
        BranchInst *se = bs.CreateCondBr(rx, ie, iw);
        PN->addIncoming(ds, iwi);
      }
    }

    errs() << "\n" << *c;
  }
  void del(Instruction *cq) {
    for (User *hf : cq->users()) {
      Instruction *udf = dyn_cast<Instruction>(hf);
      if (udf != NULL)
        del(udf);
      udf->eraseFromParent();
    }
  }
  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    AU.addRequiredTransitive<ScalarEvolutionWrapperPass>();
    AU.addRequiredTransitive<LoopInfoWrapperPass>();
  }
};
}

char Hello1::ID = 0;
static RegisterPass<Hello1>
T("hello1", "Hello World Pass (with getAnalysisUsage implemented)");

namespace {
// Hello - The first implementation, without getAnalysisUsage.
struct Hello : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  Hello() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if (F.getName() == "cttError") {
      return false;
    }
    BasicBlock *xx, *xy;
    int ablock, block, blocks = 0;
    ablock = 1;
    SmallVector<BasicBlock *, 32> NB;
    for (Function::iterator i = F.begin(); i != F.end(); i++) {
      BasicBlock *b = &*i;
      ++blocks;
    }
    for (Function::iterator i = F.begin(); i != F.end(); i++) {
      BasicBlock *b = &*i;
      xx = b;
      ablock = 1;
      NB.push_back(b);
      for (BasicBlock *suc : successors(b)) {
        ++ablock;
        NB.push_back(suc);
      }
      if (ablock == 1 || ablock == blocks) {
        NB.clear();
      } else
        break;
    }
    for (Function::iterator i = F.begin(); i != F.end(); i++) {
      BasicBlock *B = &*i;
      block = 0;
      for (BasicBlock *h : NB) {
        if (B->getName() != h->getName()) {
          ++block;
          if (block == ablock)
            xy = B;
          continue;
        } else
          break;
      }
      if (ablock == block)
        break;
    }
    Instruction *hje = xx->getTerminator();
    IRBuilder<> ds(hje);
    ds.CreateBr(xy);
    Instruction *hj = xx->getTerminator();
    hj->eraseFromParent();
    Module *j = F.getParent();
    errs() << *j << "\n";
  }
  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    //    AU.addRequiredTransitive<ScalarEvolutionWrapperPass>();
    //    AU.addRequiredTransitive<LoopInfoWrapperPass>();
  }
};
}

char Hello::ID = 0;
static RegisterPass<Hello>
G("hello", "Hello World Pass (with getAnalysisUsage implemented)");

namespace {
// Hello5 - The first implementation, without getAnalysisUsage.
struct Hello5 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  Hello5() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {

    if (F.getName() != "func") {
      return false;
    }
    int m = 0;
    Value *uq;
    Module *c = F.getParent();
    Instruction *ld, *la, *ls, *yu;
    BasicBlock *iy, *ie, *iw, *iwi;
    LLVMContext &tx = c->getContext();
    auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    ArrayRef<BasicBlock *> block;
    PHINode *PN;
    Value *ds, *jds;
    GetElementPtrInst *kun;
    LoadInst *acp;
    Instruction *pj;
    for (Loop *l : LI) {
      assert(l->getLoopLatch() && "no loop latch ");
      assert(l->getHeader() && "no loop header");
      assert(l->getExitingBlock() && "no exit block");
      iy = l->getHeader();
      iw = l->getExitingBlock();
      block = l->getBlocks();
      iwi = l->getLoopLatch();
      for (m = 0; m < block.size(); m++)
        if (block[m] != l->getHeader() && block[m] != l->getLoopLatch())
          ie = block[m];
      Instruction *iu;
      if (iy != NULL) {
        la = iy->getFirstNonPHI();
        ls = la->getNextNode();
        Instruction *yu = iy->getTerminator();
        iu = iy->getFirstNonPHI();
        IRBuilder<> bs(yu);
        Instruction *inst;
        for (m = 0; m < block.size(); m++)
          if (block[m] != l->getHeader() && block[m] != l->getLoopLatch())
            inst = block[m]->getFirstNonPHI();
        Value *bq = bs.CreateSub(iu, bs.getInt32(2));
        uq = bs.CreateGEP(inst, bq);
        acp = bs.CreateLoad(uq);
      }

      if (ie != NULL) {
        ld = ie->getFirstNonPHI();
        ld->moveBefore(iu);
        Instruction *yu = ie->getFirstNonPHI();
        IRBuilder<> bs(yu);
        PN = bs.CreatePHI(Type::getInt32Ty(tx), 2, "five");
        PN->addIncoming(acp, iy);
        for (Instruction &a : *ie) {
          GetElementPtrInst *gm = dyn_cast<GetElementPtrInst>(&a);
          if (gm != NULL) {
            Instruction *cgf = gm;
            Instruction *cq = gm->getNextNode();
            del(cq);
            cq->eraseFromParent();
            cgf->eraseFromParent();
            Instruction *iop = ie->getFirstNonPHI();
            del(iop);
            iop->eraseFromParent();
            break;
          }
        }
        for (Instruction &a : *ie) {
          GetElementPtrInst *gm = dyn_cast<GetElementPtrInst>(&a);
          if (gm != NULL) {
            kun = gm;
          }
        }
        IRBuilder<> bf(kun);
        Instruction *vc = ie->getFirstNonPHI();
        Instruction *vcc = vc->getNextNode();
        Value *subb = bf.CreateSub(vcc, bf.getInt32(2));
        jds = bf.CreateAdd(PN, bf.getInt32(2));
        ds = bf.CreateSub(jds, subb);
        Instruction *oops = ie->getTerminator();
        IRBuilder<> bqq(oops);
        StoreInst *st = bqq.CreateStore(ds, kun);
      }
      if (iwi != NULL) {
        yu = iwi->getTerminator();
        IRBuilder<> bs(yu);
        Instruction *loas = la->clone();
        Instruction *load = ls->clone();
        loas->insertBefore(yu);
        load->insertBefore(yu);
        Value *rx = bs.CreateICmpSLT(loas, load);
        yu = iwi->getTerminator();
        yu->eraseFromParent();
        bs.SetInsertPoint(iwi);
        BranchInst *se = bs.CreateCondBr(rx, ie, iw);
        PN->addIncoming(jds, iwi);
      }
    }

    errs() << "\n" << *c;
  }
  void del(Instruction *cq) {
    for (User *hf : cq->users()) {
      Instruction *udf = dyn_cast<Instruction>(hf);
      if (udf != NULL)
        del(udf);
      udf->eraseFromParent();
    }
  }

  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    AU.addRequiredTransitive<ScalarEvolutionWrapperPass>();
    AU.addRequiredTransitive<LoopInfoWrapperPass>();
  }
};
}

char Hello5::ID = 0;
static RegisterPass<Hello5>
H("hello5", "Hello World Pass (with getAnalysisUsage implemented)");

/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2011 by Dimitri van Heesch.
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation under the terms of the GNU General Public License is hereby 
 * granted. No representations are made about the suitability of this software 
 * for any purpose. It is provided "as is" without express or implied warranty.
 * See the GNU General Public License for more details.
 *
 * Documents produced by Doxygen are derivative works derived from the
 * input used in their production; they are not affected by this license.
 *
 */

#include "membername.h"
#include "classdef.h"
#include "util.h"
#include "filedef.h"

MemberName::MemberName(const char *n) : QList<MemberDef>()
{
  name=n;
  setAutoDelete(TRUE);
}

MemberName::~MemberName()
{
}

int MemberName::compareItems(GCI item1, GCI item2)
{
  MemberDef *m1=(MemberDef *)item1;
  MemberDef *m2=(MemberDef *)item2;
  ClassDef *c1=m1->getClassDef();
  ClassDef *c2=m2->getClassDef();
  FileDef  *f1=m1->getFileDef();
  FileDef  *f2=m2->getFileDef();
  if (c1 && c2)
    return strcmp(c1->name(),c2->name());
  else if (f1 && f2)
    return strcmp(f1->name(),f2->name());
  else 
    return 0;
}

MemberNameInfo::MemberNameInfo(const char *n) : QList<MemberInfo>()
{
  name=n;
  setAutoDelete(TRUE);
}

int MemberNameInfo::compareItems(GCI item1, GCI item2)
{
  MemberInfo *m1=(MemberInfo *)item1;
  MemberInfo *m2=(MemberInfo *)item2;
  ClassDef *c1=m1->memberDef->getClassDef();
  ClassDef *c2=m2->memberDef->getClassDef();
  FileDef  *f1=m1->memberDef->getFileDef();
  FileDef  *f2=m2->memberDef->getFileDef();
  if (c1 && c2)
    return strcmp(c1->name(),c2->name());
  else if (f1 && f2)
    return strcmp(f1->name(),f2->name());
  else 
    return 0;
}
MemberNameIterator::MemberNameIterator(const MemberName &mnlist) :
  QListIterator<MemberDef>(mnlist)
{
}

int MemberNameSDict::compareItems(GCI item1, GCI item2)
{
  MemberName *n1=(MemberName *)item1;
  MemberName *n2=(MemberName *)item2;
  return stricmp(n1->memberName()+getPrefixIndex(n1->memberName()),
                 n2->memberName()+getPrefixIndex(n2->memberName())
                );
}


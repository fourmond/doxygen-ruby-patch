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

/*
 * translator_jp.h 
 * Updates:
 * 1.2.5)
 * First Translation
 *      by Kenji Nagamatsu
 * 1.2.12)
 * Update and Shift-Jis(_WIN32)
 *      by Ryunosuke Sato (30-Dec-2001)
 * 1.5.8)
 * Translation for 1.5.8.
 *      by Hiroki Iseri (18-Feb-2009)
 */

#ifndef TRANSLATOR_JP_H
#define TRANSLATOR_JP_H

class TranslatorJapanese : public TranslatorAdapter_1_6_0
{
 private:
  /*! The decode() can change euc into sjis */
  inline QCString decode(const QCString & sInput)
  {
    //if (Config_getBool("USE_WINDOWS_ENCODING"))
    //{
    //  return JapaneseEucToSjis(sInput);
    //}
    //else
    //{
      return sInput;
    //}
  }
  public:
    virtual QCString idLanguage()
    { return "japanese"; }
    virtual QCString latexLanguageSupportCommand()
    {
      return "";
    }
    /*! returns the name of the package that is included by LaTeX */
    virtual QCString idLanguageCharset()
    {
      //if (Config_getBool("USE_WINDOWS_ENCODING"))
      //{
      //  return "Shift_JIS";
      //}
      //else
      //{
        return "euc-jp";
      //}
    }

    /*! used in the compound documentation before a list of related functions. */
    virtual QCString trRelatedFunctions()
    { return decode("��Ϣ����ؿ�"); }

    /*! subscript for the related functions. */
    virtual QCString trRelatedSubscript()
    { return decode("�ʤ����ϥ᥽�åɤǤʤ����Ȥ���ա�"); }

    /*! header that is put before the detailed description of files, classes and namespaces. */
    virtual QCString trDetailedDescription()
    { return decode("����"); }

    /*! header that is put before the list of typedefs. */
    virtual QCString trMemberTypedefDocumentation()
    { return decode("�����"); }

    /*! header that is put before the list of enumerations. */
    virtual QCString trMemberEnumerationDocumentation()
    { return decode("���"); }

    /*! header that is put before the list of member functions. */
    virtual QCString trMemberFunctionDocumentation()
    { 
	  if( Config_getBool("OPTIMIZE_OUTPUT_JAVA"))
	  {
		return decode("�᥽�å�");
	  }
	  else
	  {
		return decode("�ؿ�");
	  }
	}

    /*! header that is put before the list of member attributes. */
    virtual QCString trMemberDataDocumentation()
    {
      if( Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
	    return decode("��¤��");
	  }
      else
	  {
	    return decode("�ѿ�");
	  }
    }

    /*! this is the text of a link put after brief descriptions. */
	virtual QCString trMore()
    { return decode("[�ܺ�]"); }

    /*! put in the class documentation */
    virtual QCString trListOfAllMembers()
    { return decode("���٤ƤΥ��а���"); }

    /*! used as the title of the "list of all members" page of a class */
    virtual QCString trMemberList()
    { return decode("���а���"); }

    /*! this is the first part of a sentence that is followed by a class name */
    virtual QCString trThisIsTheListOfAllMembers()
    { return decode("����������Фΰ����Ǥ���"); }

    /*! this is the remainder of the sentence after the class name */
    virtual QCString trIncludingInheritedMembers()
    { return decode("�Ѿ����Ф�ޤ�Ǥ��ޤ���"); }

    /*! this is put at the author sections at the bottom of man pages.
     *  parameter s is name of the project name.
     */
    virtual QCString trGeneratedAutomatically(const char *s)
    { QCString result;
      if (s) result=(QCString)s+decode("��");
      result+=decode("���������� Doxygen �ˤ���������ޤ�����");
      return result;
    }

    /*! put after an enum name in the list of all members */
    virtual QCString trEnumName()
    { return decode("Enum"); }

    /*! put after an enum value in the list of all members */
    virtual QCString trEnumValue()
    { return decode("Enum ��"); }

    /*! put after an undocumented member in the list of all members */
    virtual QCString trDefinedIn()
    { return decode("�����������Ƥ��ޤ���"); }

    // quick reference sections

    /*! This is put above each page as a link to the list of all groups of
     *  compounds or files (see the \\group command).
     */
    virtual QCString trModules()
    { return decode("�⥸�塼��"); }

    /*! This is put above each page as a link to the class hierarchy */
    virtual QCString trClassHierarchy()
    { return decode("���饹����"); }

    /*! This is put above each page as a link to the list of annotated classes */
    virtual QCString trCompoundList()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ�����¤");
	}
      else
	{
	  return decode("����");
	}
    }

    /*! This is put above each page as a link to the list of documented files */
    virtual QCString trFileList()
    { return decode("�ե��������"); }

    /*! This is put above each page as a link to the list of all verbatim headers */
    virtual QCString trHeaderFiles()
    { return decode("�إå��ե�����"); }

    /*! This is put above each page as a link to all members of compounds. */
    virtual QCString trCompoundMembers()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ����ե������");
	}
      else
	{
	  return decode("��������");
	}
    }

    /*! This is put above each page as a link to all members of files. */
    virtual QCString trFileMembers()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�����Х�");
	}
      else
	{
	  return decode("�ե��������");
	}
    }
    /*! This is put above each page as a link to all related pages. */
    virtual QCString trRelatedPages()
    { return decode("��Ϣ�ڡ���"); }

    /*! This is put above each page as a link to all examples. */
    virtual QCString trExamples()
    { return decode("��"); }

    /*! This is put above each page as a link to the search engine. */
    virtual QCString trSearch()
    { return decode("����"); }

    /*! This is an introduction to the class hierarchy. */
    virtual QCString trClassHierarchyDescription()
    { return decode("���ηѾ������Ϥ����ޤ��ˤϥ����Ȥ���Ƥ��ޤ�����"
             "�����˥���ե��٥åȽ�ǥ����Ȥ���ƤϤ��ޤ���");
    }

    /*! This is an introduction to the list with all files. */
    virtual QCString trFileListDescription(bool /*extractAll*/)
    {
      QCString result=decode("�����");
      result+=decode("�ե���������Ǥ���");
      return result;
    }

    /*! This is an introduction to the annotated compound list. */
    virtual QCString trCompoundListDescription()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ�����¤�������Ǥ���");
	}
      else
	{
	  return decode("���饹����¤�Ρ������Ρ����󥿥ե������������Ǥ���");
	}
    }

    /*! This is an introduction to the page with all class members. */
    virtual QCString trCompoundMembersDescription(bool extractAll)
    {
      QCString result=decode("�����");
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
	    result+=decode("�ե�����ɤΰ����Ǥ��줾��");
	    if (extractAll) result+=decode("��°���Ƥ��빽¤��/������");
	  }
      else
	  {
	    result+=decode("���饹���Фΰ����ǡ����줾��");
	    if (extractAll) result+=decode("��°���Ƥ��륯�饹");
	  }
      result+=decode("�������إ�󥯤��Ƥ��ޤ���");
      return result;
    }

    /*! This is an introduction to the page with all file members. */
    virtual QCString trFileMembersDescription(bool /*extractAll*/)
    {
      QCString result=decode("�����");
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  result+=decode("�ؿ����ѿ����ޥ���Enum��Typedef ��");
	}
      else
	{
	  result+=decode("�ե�������Ф�");
	}
      result+=decode("�����Ǥ������줾�줬°���Ƥ���ե�����������إ�󥯤��Ƥ��ޤ���");
      return result;
    }

    /*! This is an introduction to the page with the list of all header files. */
    virtual QCString trHeaderFilesDescription()
    { return decode("API��������إå��ե�����Ǥ���"); }

    /*! This is an introduction to the page with the list of all examples */
    virtual QCString trExamplesDescription()
    { return decode("���٤Ƥ���ΰ����Ǥ���"); }

    /*! This is an introduction to the page with the list of related pages */
    virtual QCString trRelatedPagesDescription()
    { return decode("��Ϣ�ڡ����ΰ����Ǥ���"); }

    /*! This is an introduction to the page with the list of class/file groups */
    virtual QCString trModulesDescription()
    { return decode("���٤ƤΥ⥸�塼��ΰ����Ǥ���"); }

    /*! This sentences is used in the annotated class/file lists if no brief
     * description is given.
     */
    virtual QCString trNoDescriptionAvailable()
    { return decode("�ɥ�����Ȥ����Ҥ���Ƥ��ޤ���"); }

    // index titles (the project name is prepended for these)


    /*! This is used in HTML as the title of index.html. */
    virtual QCString trDocumentation()
    { return decode("�ɥ������"); }

    /*! This is used in LaTeX as the title of the chapter with the
     * index of all groups.
     */
    virtual QCString trModuleIndex()
    { return decode("�⥸�塼�����"); }

    /*! This is used in LaTeX as the title of the chapter with the
     * class hierarchy.
     */
    virtual QCString trHierarchicalIndex()
    { return decode("���غ���"); }

    /*! This is used in LaTeX as the title of the chapter with the
     * annotated compound index.
     */
    virtual QCString trCompoundIndex()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ�����¤����");
	}
      else
	{
	  return decode("��������");
	}
    }

    /*! This is used in LaTeX as the title of the chapter with the
     * list of all files.
     */
    virtual QCString trFileIndex()
    { return decode("�ե��������"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all groups.
     */
    virtual QCString trModuleDocumentation()
    { return decode("�⥸�塼��"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all classes, structs and unions.
     */
    virtual QCString trClassDocumentation()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ�����¤");
	}
      else
	{
	  return decode("���饹");
	}
    }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all files.
     */
    virtual QCString trFileDocumentation()
    { return decode("�ե�����"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all examples.
     */
    virtual QCString trExampleDocumentation()
    { return decode("��"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all related pages.
     */
    virtual QCString trPageDocumentation()
    { return decode("�ڡ���"); }

    /*! This is used in LaTeX as the title of the document */
    virtual QCString trReferenceManual()
    { return decode("��ե���󥹥ޥ˥奢��"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of defines
     */
    virtual QCString trDefines()
    { return decode("�ޥ������"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of function prototypes
     */
    virtual QCString trFuncProtos()
    { return decode("�ؿ��ץ�ȥ�����"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of typedefs
     */
    virtual QCString trTypedefs()
    { return decode("�����"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of enumerations
     */
    virtual QCString trEnumerations()
    { return decode("���"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of (global) functions
     */
    virtual QCString trFunctions()
    { return decode("�ؿ�"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of (global) variables
     */
    virtual QCString trVariables()
    { return decode("�ѿ�"); }

    /*! This is used in the documentation of a file as a header before the
     *  list of (global) variables
     */
    virtual QCString trEnumerationValues()
      { return decode("��󷿤���"); }
    /*! This is used in the documentation of a file before the list of
     *  documentation blocks for defines
     */
    virtual QCString trDefineDocumentation()
    { return decode("�ޥ������"); }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for function prototypes
     */
    virtual QCString trFunctionPrototypeDocumentation()
    { return decode("�ؿ��ץ�ȥ�����"); }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for typedefs
     */
    virtual QCString trTypedefDocumentation()
    { return decode("�����"); }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for enumeration types
     */
    virtual QCString trEnumerationTypeDocumentation()
    { return decode("���"); }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for functions
     */
    virtual QCString trFunctionDocumentation()
    { return decode("�ؿ�"); }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for variables
     */
    virtual QCString trVariableDocumentation()
    { return decode("�ѿ�"); }

    /*! This is used in the documentation of a file/namespace/group before
     *  the list of links to documented compounds
     */
    virtual QCString trCompounds()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ�����¤");
	}
      else
	{
	  return decode("����");
	}
    }
    /*! This is used in the standard footer of each page and indicates when
     *  the page was generated
     */
    virtual QCString trGeneratedAt(const char *date,const char *projName)
    {
      QCString result;
      if (projName) result+=(QCString)projName+decode("���Ф���");
      result+=(QCString)date+decode("����������ޤ�����");
      return result;
    }
    /*! This is part of the sentence used in the standard footer of each page.
     */
    virtual QCString trWrittenBy()
    {
      return decode("���");
    }

    /*! this text is put before a class diagram */
    virtual QCString trClassDiagram(const char *clName)
    {
      return (QCString)clName+decode("���Ф���Ѿ������");
    }

    /*! this text is generated when the \\internal command is used. */
    virtual QCString trForInternalUseOnly()
    { return decode("�������ѤΤߡ�"); }

    /*! this text is generated when the \\reimp command is used. */
    virtual QCString trReimplementedForInternalReasons()
    { return decode("����Ū����ͳ�ˤ��Ƽ�������ޤ�������API�ˤϱƶ����ޤ���");
    }

    /*! this text is generated when the \\warning command is used. */
    virtual QCString trWarning()
    { return decode("�ٹ�"); }

    /*! this text is generated when the \\bug command is used. */
    virtual QCString trBugsAndLimitations()
    { return decode("�Х�������"); }

    /*! this text is generated when the \\version command is used. */
    virtual QCString trVersion()
    { return decode("�С������"); }

    /*! this text is generated when the \\date command is used. */
    virtual QCString trDate()
    { return decode("����"); }

    /*! this text is generated when the \\return command is used. */
    virtual QCString trReturns()
    { return decode("�����"); }

    /*! this text is generated when the \\sa command is used. */
    virtual QCString trSeeAlso()
    { return decode("����"); }

    /*! this text is generated when the \\param command is used. */
    virtual QCString trParameters()
    { return decode("����"); }

    /*! this text is generated when the \\exception command is used. */
    virtual QCString trExceptions()
    { return decode("�㳰"); }

    /*! this text is used in the title page of a LaTeX document. */
    virtual QCString trGeneratedBy()
    { return decode("������"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990307
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of page containing all the index of all namespaces. */
    virtual QCString trNamespaceList()
    { return decode("�͡��ॹ�ڡ�������"); }

    /*! used as an introduction to the namespace list */
    virtual QCString trNamespaceListDescription(bool /*extractAll*/)
    {
      QCString result=decode("");
      result+=decode("�͡��ॹ�ڡ����ΰ����Ǥ���");
      return result;
    }

    /*! used in the class documentation as a header before the list of all
     *  friends of a class
     */
    virtual QCString trFriends()
    { return decode("�ե���"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////

    /*! used in the class documentation as a header before the list of all
     * related classes
     */
    virtual QCString trRelatedFunctionDocumentation()
    { return decode("�ե��ɤȴ�Ϣ����ؿ�"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of the HTML page of a class/struct/union */
    virtual QCString trCompoundReference(const char *clName,
                                 ClassDef::CompoundType compType,
                                 bool isTemplate)
    {
      QCString result="";
      switch(compType)
      {
        case ClassDef::Class:      result+=decode("���饹 "); break;
        case ClassDef::Struct:     result+=decode("��¤�� "); break;
        case ClassDef::Union:      result+=decode("������ "); break;
        case ClassDef::Interface:  result+=decode("���󥿥ե����� "); break;
        case ClassDef::Protocol:   result+=decode("�ץ�ȥ��� "); break;
        case ClassDef::Category:   result+=decode("���ƥ��� "); break;
        case ClassDef::Exception:  result+=decode("�㳰 "); break;
      }
      if (isTemplate) result+=decode("�ƥ�ץ졼�� ");
      result+=(QCString)clName;
      return result;
    }

    /*! used as the title of the HTML page of a file */
    virtual QCString trFileReference(const char *fileName)
    {
      QCString result=decode("")+(QCString)fileName;
      return result;
    }

    /*! used as the title of the HTML page of a namespace */
    virtual QCString trNamespaceReference(const char *namespaceName)
    {
      QCString result=decode("�͡��ॹ�ڡ��� ")+(QCString)namespaceName;
      return result;
    }

    /* these are for the member sections of a class, struct or union */
    virtual QCString trPublicMembers()
    { return decode("Public �᥽�å�"); }
    virtual QCString trPublicSlots()
    { return decode("Public ����å�"); }
    virtual QCString trSignals()
    { return decode("�����ʥ�"); }
    virtual QCString trStaticPublicMembers()
    { return decode("Static Public �᥽�å�"); }
    virtual QCString trProtectedMembers()
    { return decode("Protected �᥽�å�"); }
    virtual QCString trProtectedSlots()
    { return decode("Protected ����å�"); }
    virtual QCString trStaticProtectedMembers()
    { return decode("Static Protected �᥽�å�"); }
    virtual QCString trPrivateMembers()
    { return decode("Private �᥽�å�"); }
    virtual QCString trPrivateSlots()
    { return decode("Private ����å�"); }
    virtual QCString trStaticPrivateMembers()
    { return decode("Static Private �᥽�å�"); }

    /*! this function is used to produce a comma-separated list of items.
     *  use generateMarker(i) to indicate where item i should be put.
     */
    virtual QCString trWriteList(int numEntries)
    {
      QCString result;
      int i;
      // the inherits list contain `numEntries' classes
      for (i=0;i<numEntries;i++)
      {
        // use generateMarker to generate placeholders for the class links!
        result+=generateMarker(i); // generate marker for entry i in the list
                                   // (order is left to right)

        if (i!=numEntries-1)  // not the last entry, so we need a separator
        {
          if (i<numEntries-2) // not the fore last entry
            result+=decode(", ");
          else                // the fore last entry
            result+=decode(", �� ");
        }
      }
      return result;
    }

    /*! used in class documentation to produce a list of base classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritsList(int numEntries)
    {
      return trWriteList(numEntries)+decode("��Ѿ����Ƥ��ޤ���");
    }

    /*! used in class documentation to produce a list of super classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritedByList(int numEntries)
    {
      return trWriteList(numEntries)+decode("�˷Ѿ�����Ƥ��ޤ���");
    }

    /*! used in member documentation blocks to produce a list of
     *  members that are hidden by this one.
     */
    virtual QCString trReimplementedFromList(int numEntries)
    {
      return trWriteList(numEntries)+decode("���������Ƥ��ޤ���");
    }

    /*! used in member documentation blocks to produce a list of
     *  all member that overwrite the implementation of this member.
     */
    virtual QCString trReimplementedInList(int numEntries)
    {
      return trWriteList(numEntries)+decode("�Ǻ��������Ƥ��ޤ���");
    }

    /*! This is put above each page as a link to all members of namespaces. */
    virtual QCString trNamespaceMembers()
    { return decode("�͡��ॹ�ڡ�������"); }

    /*! This is an introduction to the page with all namespace members */
    virtual QCString trNamespaceMemberDescription(bool extractAll)
    {
	QCString result=decode("�����");
      result+=decode("�͡��ॹ�ڡ����ΰ����Ǥ������줾��");
      if (extractAll)
	  result+=decode("�Υ͡��ॹ�ڡ���");
      else
	  result+=decode("��°���Ƥ���͡��ॹ�ڡ���");
      result+=decode("�إ�󥯤��Ƥ��ޤ���");
      return result;
    }
    /*! This is used in LaTeX as the title of the chapter with the
     *  index of all namespaces.
     */
    virtual QCString trNamespaceIndex()
    { return decode("�͡��ॹ�ڡ�������"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all namespaces.
     */
    virtual QCString trNamespaceDocumentation()
    { return decode("�͡��ॹ�ڡ���"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

    /*! This is used in the documentation before the list of all
     *  namespaces in a file.
     */
    virtual QCString trNamespaces()
    { return decode("�͡��ॹ�ڡ���"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990728
//////////////////////////////////////////////////////////////////////////

    /*! This is put at the bottom of a class documentation page and is
     *  followed by a list of files that were used to generate the page.
     */
    virtual QCString trGeneratedFromFiles(ClassDef::CompoundType compType,
        bool)
    { // here s is one of " Class", " Struct" or " Union"
      // single is true implies a single file
      QCString result=(QCString)decode("����");
      switch(compType)
      {
        case ClassDef::Class:      result+=decode("���饹"); break;
        case ClassDef::Struct:     result+=decode("��¤��"); break;
        case ClassDef::Union:      result+=decode("������"); break;
        case ClassDef::Interface:  result+=decode("���󥿥ե�����"); break;
        case ClassDef::Protocol:   result+=decode("�ץ�ȥ���"); break;
        case ClassDef::Category:   result+=decode("���ƥ���"); break;
        case ClassDef::Exception:  result+=decode("�㳰"); break;
      }
      result+=decode("�������ϼ��Υե����뤫����������ޤ���:");
      return result;
    }

    /*! This is in the (quick) index as a link to the alphabetical compound
     * list.
     */
    virtual QCString trAlphabeticalList()
    { return decode("����ե��٥åȽ����"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the heading text for the retval command. */
    virtual QCString trReturnValues()
    { return decode("�����"); }

    /*! This is in the (quick) index as a link to the main page (index.html)
     */
    virtual QCString trMainPage()
    { return decode("�ᥤ��ڡ���"); }

    /*! This is used in references to page that are put in the LaTeX
     *  documentation. It should be an abbreviation of the word page.
     */
    virtual QCString trPageAbbreviation()
    { return decode("p."); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991003
//////////////////////////////////////////////////////////////////////////

    virtual QCString trSources()
    {
      return decode("������");
    }
    virtual QCString trDefinedAtLineInSourceFile()
    {
      return decode(" @1 �� @0 �Ԥ��������Ƥ��ޤ���");
    }
    virtual QCString trDefinedInSourceFile()
    {
      return decode(" @0 ���������Ƥ��ޤ���");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDeprecated()
    {
      return decode("��侩");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////

    /*! this text is put before a collaboration diagram */
    virtual QCString trCollaborationDiagram(const char *clName)
    {
      return (QCString)clName+decode("�Υ���ܥ졼������");
    }
    /*! this text is put before an include dependency graph */
    virtual QCString trInclDepGraph(const char *fName)
    {
	return (QCString)fName+decode("�Υ��󥯥롼�ɰ�¸�ط���");
    }
    /*! header that is put before the list of constructor/destructors. */
    virtual QCString trConstructorDocumentation()
    {
      return decode("���󥹥ȥ饯���ȥǥ��ȥ饯��");
    }
    /*! Used in the file documentation to point to the corresponding sources. */
    virtual QCString trGotoSourceCode()
    {
      return decode("�����������ɤ򸫤롣");
    }
    /*! Used in the file sources to point to the corresponding documentation. */
    virtual QCString trGotoDocumentation()
    {
      return decode("�����򸫤롣");
    }
    /*! Text for the \\pre command */
    virtual QCString trPrecondition()
    {
      return decode("�������");
    }
    /*! Text for the \\post command */
    virtual QCString trPostcondition()
    {
      return decode("������");
    }
    /*! Text for the \\invariant command */
    virtual QCString trInvariant()
    {
      return decode("����");
    }
    /*! Text shown before a multi-line variable/enum initialization */
    virtual QCString trInitialValue()
    {
      return decode("�����:");
    }
    /*! Text used the source code in the file index */
    virtual QCString trCode()
    {
      return decode("������");
    }
    virtual QCString trGraphicalHierarchy()
    {
      return decode("���饹���ؿ�");
    }
    virtual QCString trGotoGraphicalHierarchy()
    {
      return decode("���饹���ؿޤ򸫤롣");
    }
    virtual QCString trGotoTextualHierarchy()
    {
      return decode("���饹���ؿޤ򸫤롣");
    }
    virtual QCString trPageIndex()
    {
      return decode("�ڡ�������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////

    virtual QCString trNote()
    {
      return decode("�Ф���");
    }
    virtual QCString trPublicTypes()
    {
      return decode("Public ��");
    }
    virtual QCString trPublicAttribs()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ѿ�");
	}
      else
	{
	  return decode("Public �ѿ�");
	}
    }
    virtual QCString trStaticPublicAttribs()
    {
      return decode("Static Public �ѿ�");
    }
    virtual QCString trProtectedTypes()
    {
      return decode("Protected ��");
    }
    virtual QCString trProtectedAttribs()
    {
      return decode("Protected �ѿ�");
    }
    virtual QCString trStaticProtectedAttribs()
    {
      return decode("Static Protected �ѿ�");
    }
    virtual QCString trPrivateTypes()
    {
      return decode("Private ��");
    }
    virtual QCString trPrivateAttribs()
    {
      return decode("Private �ѿ�");
    }
    virtual QCString trStaticPrivateAttribs()
    {
      return decode("Static Private �ѿ�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a todo item */
    virtual QCString trTodo()
    {
      return decode("TODO");
    }
    /*! Used as the header of the todo list */
    virtual QCString trTodoList()
    {
      return decode("TODO����");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

    virtual QCString trReferencedBy()
    {
      return decode("���ȸ�");
    }
    virtual QCString trRemarks()
    {
      return decode("�ո�");
    }
    virtual QCString trAttention()
    {
      return decode("���");
    }
    virtual QCString trInclByDepGraph()
    {
	return decode("���Υ���դϡ��ɤΥե����뤫��ľ�ܡ�����Ū��"
             "���󥯥롼�ɤ���Ƥ��뤫�򼨤��Ƥ��ޤ���");
    }
    virtual QCString trSince()
    {
      return decode("����");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

    /*! title of the graph legend page */
    virtual QCString trLegendTitle()
    {
      return decode("����դ�����");
    }
    /*! page explaining how the dot graph's should be interpreted */
    virtual QCString trLegendDocs()
    {
      return
        decode("���Υڡ����Ǥϡ�doxygen ���������줿����դ�ɤΤ褦�ˤߤ���褤����"
        "�������ޤ���<p>\n"
        "�������ͤ��Ƥߤޤ���\n"
        "\\code\n"
        "/*! ��ά����Ƹ����ʤ����饹 */\n"
        "class Invisible { };\n\n"
        "/*! ��ά���줿���饹(�Ѿ��ط��ϱ�����Ƥ���) */\n"
        "class Truncated : public Invisible { };\n\n"
        "/* doxygen �����Ȥˤ��ɥ�����Ȥ��ʤ����饹 */\n"
        "class Undocumented { };\n\n"
        "/*! public �ǷѾ����줿���饹 */\n"
        "class PublicBase : public Truncated { };\n\n"
        "/*! A template class */\n"
        "template<class T> class Templ { };\n\n"
        "/*! protected �ǷѾ����줿���饹 */\n"
        "class ProtectedBase { };\n\n"
        "/*! private �ǷѾ����줿���饹 */\n"
        "class PrivateBase { };\n\n"
        "/*! �Ѿ����줿���饹�ǻȤ��Ƥ��륯�饹 */\n"
        "class Used { };\n\n"
        "/*! ʣ���Υ��饹��Ѿ����Ƥ����̥��饹 */\n"
        "class Inherited : public PublicBase,\n"
        "                  protected ProtectedBase,\n"
        "                  private PrivateBase,\n"
        "                  public Undocumented,\n"
        "                  public Templ<int>\n"
        "{\n"
        "  private:\n"
        "    Used *m_usedClass;\n"
        "};\n"
        "\\endcode\n"
        "����ե�������ǡ����� \\c MAX_DOT_GRAPH_HEIGHT �� 200 �˥��åȤ��줿"
        "��硢���Τ褦�ʥ���դȤʤ�ޤ���"
        "<p><center><img src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
        "<p>\n"
        "��Υ������Υܥå����ˤϼ��Τ褦�ʰ�̣������ޤ���\n"
        "<ul>\n"
        "<li>�����ɤ�Ĥ֤��줿�ܥå����ϡ����Υ���դ��б����빽¤�Τ䥯�饹��"
        "ɽ���ޤ���\n"
        "<li>���ȤΥܥå����ϥɥ�����Ȥ����빽¤�Τ䥯�饹��ɽ���ޤ���\n"
        "<li>�������ȤΥܥå����ϥɥ�����Ȥ��ʤ���¤�Τ䥯�饹��ɽ���ޤ���\n"
        "<li>���ȤΥܥå����ϥɥ�����Ȥ����빽¤�Τ䥯�饹��ɽ���ޤ�����"
	  "���ꤵ�줿�������˼��ޤ�ʤ�����˷Ѿ�����޴ط��򤹤٤ƿ޼�����"
	  "���Ȥ��Ǥ��ʤ��ä����Ȥ򼨤��ޤ���"
        "</ul>\n"
        "����ˤϼ��Τ褦�ʰ�̣������ޤ���\n"
        "<ul>\n"
        "<li>�Ĥ��������ĤΥ��饹�֤� public �Ѿ��ط��򼨤��ޤ���\n"
        "<li>�Ф������ protected �Ѿ��ط��򼨤��ޤ���\n"
        "<li>�֤������ private �Ѿ��ط��򼨤��ޤ���\n"
        "<li>�����������ϡ����Υ��饹��¾�Υ��饹�˴ޤޤ�Ƥ����ꡢ"
	  "���Ѥ���Ƥ��뤳�Ȥ򼨤��ޤ����ޤ���������ؤ��Ƥ��륯�饹�乽¤�Τ�"
	  "�ɤ��ѿ��ǥ��������Ǥ��뤫������Υ�٥�Ȥ��Ƽ����Ƥ��ޤ���\n"
        "</ul>\n");
    }
    /*! text for the link to the legend page */
    virtual QCString trLegend()
    {
      return decode("����");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a test item */
    virtual QCString trTest()
    {
      return decode("�ƥ���");
    }
    /*! Used as the header of the test list */
    virtual QCString trTestList()
    {
      return decode("�ƥ��Ȱ���");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.1
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for KDE-2 IDL methods */
    virtual QCString trDCOPMethods()
    {
      return decode("DCOP�᥽�å�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.2
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for IDL properties */
    virtual QCString trProperties()
    {
      return decode("�ץ�ѥƥ�");
    }
    /*! Used as a section header for IDL property documentation */
    virtual QCString trPropertyDocumentation()
    {
      return decode("�ץ�ѥƥ�");
    }


//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

    /*! Used for Java interfaces in the summary section of Java packages */
    virtual QCString trInterfaces()
    {
      return decode("���󥿡��ե�����");
    }
    /*! Used for Java classes in the summary section of Java packages */
    virtual QCString trClasses()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	{
	  return decode("�ǡ�����¤");
	}
      else
	{
	  return decode("���饹");
	}
    }
    /*! Used as the title of a Java package */
    virtual QCString trPackage(const char *name)
    {
      return (QCString)decode("�ѥå����� ")+name;
    }
    /*! Title of the package index page */
    virtual QCString trPackageList()
    {
      return decode("�ѥå���������");
    }
    /*! The description of the package index page */
    virtual QCString trPackageListDescription()
    {
      return decode("����ϥѥå����������Ǥ���");
    }
    /*! The link name in the Quick links header for each page */
    virtual QCString trPackages()
    {
      return decode("�ѥå�����");
    }
    /*! Used as a chapter title for Latex & RTF output */
    virtual QCString trPackageDocumentation()
    {
      return decode("�ѥå�����");
    }
    /*! Text shown before a multi-line define */
    virtual QCString trDefineValue()
    {
      return decode("��:");
    }


//////////////////////////////////////////////////////////////////////////
// new since 1.2.5
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a \\bug item */
    virtual QCString trBug()
    {
      return decode("�Х�");
    }
    /*! Used as the header of the bug list */
    virtual QCString trBugList()
    {
      return decode("�Х�����");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.6
//////////////////////////////////////////////////////////////////////////

    /*! Used as ansicpg for RTF file
     *
     * The following table shows the correlation of Charset name, Charset Value and
     * <pre>
     * Codepage number:
     * Charset Name       Charset Value(hex)  Codepage number
     * ------------------------------------------------------
     * DEFAULT_CHARSET           1 (x01)
     * SYMBOL_CHARSET            2 (x02)
     * OEM_CHARSET             255 (xFF)
     * ANSI_CHARSET              0 (x00)            1252
     * RUSSIAN_CHARSET         204 (xCC)            1251
     * EE_CHARSET              238 (xEE)            1250
     * GREEK_CHARSET           161 (xA1)            1253
     * TURKISH_CHARSET         162 (xA2)            1254
     * BALTIC_CHARSET          186 (xBA)            1257
     * HEBREW_CHARSET          177 (xB1)            1255
     * ARABIC _CHARSET         178 (xB2)            1256
     * SHIFTJIS_CHARSET        128 (x80)             932
     * HANGEUL_CHARSET         129 (x81)             949
     * GB2313_CHARSET          134 (x86)             936
     * CHINESEBIG5_CHARSET     136 (x88)             950
     * </pre>
     *
     */
    virtual QCString trRTFansicp()
    {
      return "932";
    }


    /*! Used as ansicpg for RTF fcharset
     *  \see trRTFansicp() for a table of possible values.
     */
    virtual QCString trRTFCharSet()
    {
      return "128";
    }

    /*! Used as header RTF general index */
    virtual QCString trRTFGeneralIndex()
    {
      return decode("����");
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trClass(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("���饹"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trFile(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("�ե�����"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trNamespace(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("�͡��ॹ�ڡ���"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trGroup(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("���롼��"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trPage(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("�ڡ���"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trMember(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("����"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trField(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("�ե������"));
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trGlobal(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("�����Х�"));
      return result;
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

    /*! This text is generated when the \\author command is used and
     *  for the author section in man pages. */
    virtual QCString trAuthor(bool first_capital, bool singular)
    {
      first_capital = first_capital;
      singular = singular;
      QCString result(decode("���"));
      return result;
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

    /*! This text is put before the list of members referenced by a member
     */
    virtual QCString trReferences()
    {
      return decode("������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

    /*! used in member documentation blocks to produce a list of
     *  members that are implemented by this one.
     */
    virtual QCString trImplementedFromList(int numEntries)
    {
      return trWriteList(numEntries)+decode("��������Ƥ��ޤ���");
    }

    /*! used in member documentation blocks to produce a list of
     *  all members that implement this abstract member.
     */
    virtual QCString trImplementedInList(int numEntries)
    {
      return trWriteList(numEntries)+decode("�Ǽ�������Ƥ��ޤ���");
    }
//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

    /*! used in RTF documentation as a heading for the Table
     *  of Contents.
     */
    virtual QCString trRTFTableOfContents()
    {
      return decode("�ܼ�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

    /*! Used as the header of the list of item that have been 
     *  flagged deprecated 
     */
    virtual QCString trDeprecatedList()
    {
      return decode("��侩����");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.18
//////////////////////////////////////////////////////////////////////////

    /*! Used as a header for declaration section of the events found in 
     * a C# program
     */
    virtual QCString trEvents()
    {
      return decode("���٥��");
    }
    /*! Header used for the documentation section of a class' events. */
    virtual QCString trEventDocumentation()
    {
      return decode("���٥��");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a heading for a list of Java class types with package scope.
     */
    virtual QCString trPackageTypes()
    { 
      return decode("�ѥå�������η����");
    }
    /*! Used as a heading for a list of Java class functions with package 
     * scope. 
     */
    virtual QCString trPackageMembers()
    { 
      return decode("�ؿ�");
    }
    /*! Used as a heading for a list of static Java class functions with 
     *  package scope.
     */
    virtual QCString trStaticPackageMembers()
    { 
      return decode("�����ƥ��å��ؿ�");
    }
    /*! Used as a heading for a list of Java class variables with package 
     * scope.
     */
    virtual QCString trPackageAttribs()
    { 
      return decode("�ѿ�");
    }
    /*! Used as a heading for a list of static Java class variables with 
     * package scope.
     */
    virtual QCString trStaticPackageAttribs()
    { 
      return decode("�����ƥ��å��ѿ�");
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.3.1
//////////////////////////////////////////////////////////////////////////

    /*! Used in the quick index of a class/file/namespace member list page 
     *  to link to the unfiltered list of all members.
     */
    virtual QCString trAll()
    {
      return decode("����");
    }
    /*! Put in front of the call graph for a function. */
    virtual QCString trCallGraph()
    {
      return decode("�ؿ��θƤӽФ������:");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.3
//////////////////////////////////////////////////////////////////////////

    /*! When the search engine is enabled this text is put in the header 
     *  of each page before the field where one can enter the text to search 
     *  for. 
     */
    virtual QCString trSearchForIndex()
    {
      return decode("����");
    }
    /*! This string is used as the title for the page listing the search
     *  results.
     */
    virtual QCString trSearchResultsTitle()
    {
      return decode("�������");
    }
    /*! This string is put just before listing the search results. The
     *  text can be different depending on the number of documents found.
     *  Inside the text you can put the special marker $num to insert
     *  the number representing the actual number of search results.
     *  The @a numDocuments parameter can be either 0, 1 or 2, where the 
     *  value 2 represents 2 or more matches. HTML markup is allowed inside
     *  the returned string.
     */
    virtual QCString trSearchResults(int numDocuments)
    {
      if (numDocuments==0)
      {
        return decode("���Ϥ��줿���˥ޥå�����ɥ�����Ȥ�����ޤ���Ǥ���.");
      }
      else if (numDocuments==1)
      {
        return decode("���Ϥ��줿���˥ޥå�����ɥ�����Ȥ� <b>1</b> ��ߤĤ���ޤ���.");
      }
      else 
      {
        return decode("���Ϥ��줿���˥ޥå�����ɥ�����Ȥ� <b>$num</b> ��ߤĤ���ޤ���. "
                      "�Ǥ���פ��Ƥ����Τ���ɽ������ޤ�.");
      }
    }
    /*! This string is put before the list of matched words, for each search 
     *  result. What follows is the list of words that matched the query.
     */
    virtual QCString trSearchMatches()
    {
      return decode("�ޥå�����ñ��:");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.8
//////////////////////////////////////////////////////////////////////////

    /*! This is used in HTML as the title of page with source code for file filename
     */
    virtual QCString trSourceFile(QCString& filename)
    {
      return filename + decode(" �������ե�����");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.9
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the name of the chapter containing the directory
     *  hierarchy.
     */
    virtual QCString trDirIndex()
    { return decode("�ǥ��쥯�ȥ����"); }

    /*! This is used as the name of the chapter containing the documentation
     *  of the directories.
     */
    virtual QCString trDirDocumentation()
    { return decode("�ǥ��쥯�ȥ깽��"); }

    /*! This is used as the title of the directory index and also in the
     *  Quick links of an HTML page, to link to the directory hierarchy.
     */
    virtual QCString trDirectories()
    { return decode("�ǥ��쥯�ȥ�"); }

    /*! This returns a sentences that introduces the directory hierarchy. 
     *  and the fact that it is sorted alphabetically per level
     */
    virtual QCString trDirDescription()
    { return decode("���Υǥ��쥯�ȥ�����Ϥ����ޤ��ˤϥ����Ȥ���Ƥ��ޤ�����"
		    "�����˥���ե��٥åȽ�ǥ����Ȥ���ƤϤ��ޤ���");
    }

    /*! This returns the title of a directory page. The name of the
     *  directory is passed via \a dirName.
     */
    virtual QCString trDirReference(const char *dirName)
    { QCString result=dirName; result+=decode(" �ǥ��쥯�ȥ��ե����"); return result; }

    /*! This returns the word directory with or without starting capital
     *  (\a first_capital) and in sigular or plural form (\a singular).
     */
    virtual QCString trDir(bool, bool)
    { 
      return decode("�ǥ��쥯�ȥ�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.4.1
//////////////////////////////////////////////////////////////////////////

    /*! This text is added to the documentation when the \\overload command
     *  is used for a overloaded function.
     */
    virtual QCString trOverloadText()
    {
       return decode("����ϥ����С����ɤ��줿���дؿ��Ǥ���"
		     "�������Τ�����Ѱդ���Ƥ��ޤ���"
		     "���δؿ��Ȥΰ㤤�ϰ������ΤߤǤ���");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.4.6
//////////////////////////////////////////////////////////////////////////

    /*! This is used to introduce a caller (or called-by) graph */
    virtual QCString trCallerGraph()
    {
      // return "Here is the caller graph for this function:";
      return decode("�ƽФ������:");
    }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for enumeration values
     */
    virtual QCString trEnumerationValueDocumentation()
    { return decode("���"); }


//////////////////////////////////////////////////////////////////////////
// new since 1.5.4 (mainly for Fortran)
//////////////////////////////////////////////////////////////////////////
    
    /*! header that is put before the list of member subprograms (Fortran). */
    virtual QCString trMemberFunctionDocumentationFortran()
    { return decode("�ؿ�/���֥롼����"); }

    /*! This is put above each page as a link to the list of annotated data types (Fortran). */    
    virtual QCString trCompoundListFortran()
    { return decode("�ǡ�����"); }

    /*! This is put above each page as a link to all members of compounds (Fortran). */
    virtual QCString trCompoundMembersFortran()
    { return decode("�ǡ����ե������"); }
    
    /*! This is an introduction to the annotated compound list (Fortran). */
    virtual QCString trCompoundListDescriptionFortran()
    { return decode("����ϥǡ������ΰ����Ǥ�"); }
    
    /*! This is an introduction to the page with all data types (Fortran). */
    virtual QCString trCompoundMembersDescriptionFortran(bool extractAll)
    {
	  QCString result=decode("�����");
	  result+=decode("�ե�����ɤΰ����Ǥ������줾��");
	  if (extractAll)
	  {
	  	result+=decode("��°���Ƥ���ǡ�����");
	  }
	  result+=decode("�������إ�󥯤��Ƥ��ޤ���");
	  return result;
    }
	
    /*! This is used in LaTeX as the title of the chapter with the 
     * annotated compound index (Fortran).
     */
    virtual QCString trCompoundIndexFortran()
    { return decode("�ǡ���������"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all data types (Fortran).
     */
    virtual QCString trTypeDocumentation()
    { return decode("�ǡ�����"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) subprograms (Fortran).
     */
    virtual QCString trSubprograms()
    { return decode("�ؿ�/���֥롼����"); }


    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for subprograms (Fortran)
     */
    virtual QCString trSubprogramDocumentation()
    { return decode("�ؿ�/���֥롼����"); }

    /*! This is used in the documentation of a file/namespace/group before 
     *  the list of links to documented compounds (Fortran)
     */
     virtual QCString trDataTypes()
    { return decode("�ǡ�����"); }
    
    /*! used as the title of page containing all the index of all modules (Fortran). */
    virtual QCString trModulesList()
    { return decode("�⥸�塼�����"); }

    /*! used as an introduction to the modules list (Fortran) */
    virtual QCString trModulesListDescription(bool extractAll)
    {
      QCString result=decode("�����");
      if (!extractAll) result+=decode("�������줿");
      result+=decode("�⥸�塼������Ǥ�");
      return result;
    }

    /*! used as the title of the HTML page of a module/type (Fortran) */
    virtual QCString trCompoundReferenceFortran(const char *clName,
                                    ClassDef::CompoundType compType,
                                    bool isTemplate)
    {
      QCString result="";
      switch(compType)
      {
        case ClassDef::Class:      result+=decode("�⥸�塼�� "); break;
        case ClassDef::Struct:     result+=decode("TYPE "); break;
        case ClassDef::Union:      result+=decode("������ "); break;
        case ClassDef::Interface:  result+=decode("���󥿡��ե����� "); break;
        case ClassDef::Protocol:   result+=decode("�ץ�ȥ��� "); break;
        case ClassDef::Category:   result+=decode("���ƥ��� "); break;
        case ClassDef::Exception:  result+=decode("�㳰 "); break;
      }
      if (isTemplate) result += decode("�ƥ�ץ졼�� ");
      result+=(QCString)clName;
      return result;
    }
    /*! used as the title of the HTML page of a module (Fortran) */
    virtual QCString trModuleReference(const char *namespaceName)
    {
      QCString result=namespaceName;
      result+=decode("�⥸�塼��");        
      return result;
    }
    
    /*! This is put above each page as a link to all members of modules. (Fortran) */
    virtual QCString trModulesMembers()
    { return decode("�⥸�塼�����"); }

    /*! This is an introduction to the page with all modules members (Fortran) */
    virtual QCString trModulesMemberDescription(bool extractAll)
    { 
      QCString result=decode("����ϥ⥸�塼����а����Ǥ������줾�� ");
      if (extractAll) 
      {
        result+=decode("°���Ƥ���⥸�塼��");
      }
	  result+=decode("�������إ�󥯤��Ƥ��ޤ���");
      return result;
    }

    /*! This is used in LaTeX as the title of the chapter with the 
     *  index of all modules (Fortran).
     */
    virtual QCString trModulesIndex()
    { return decode("�⥸�塼�����"); }
    
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trModule(bool /*first_capital*/, bool /*singular*/)
    {       
      return decode("�⥸�塼��");
    }
    /*! This is put at the bottom of a module documentation page and is
     *  followed by a list of files that were used to generate the page.
     */
    virtual QCString trGeneratedFromFilesFortran(ClassDef::CompoundType compType,
        bool /*single*/)
    { // here s is one of " Module", " Struct" or " Union"
      // single is true implies a single file
      QCString result="";
      switch(compType)
      {
        case ClassDef::Class:      result+=decode("�⥸�塼��"); break;
        case ClassDef::Struct:     result+=decode("TYPE"); break;
        case ClassDef::Union:      result+=decode("������"); break;
        case ClassDef::Interface:  result+=decode("���󥿡��ե�����"); break;
        case ClassDef::Protocol:   result+=decode("�ץ�ȥ���"); break;
        case ClassDef::Category:   result+=decode("���ƥ���"); break;
        case ClassDef::Exception:  result+=decode("�㳰"); break;
      }
      result+=decode(decode("�������ϼ��Υե����뤫����������ޤ���:"));
      return result;
    }
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trType(bool /*first_capital*/, bool /*singular*/)
    { 
      QCString result = decode("TYPE");
      return result; 
    }
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trSubprogram(bool /*first_capital*/, bool /*singular*/)
    { 
      QCString result = decode("���֥ץ����");
      return result; 
    }

    /*! C# Type Constraint list */
    virtual QCString trTypeConstraints()
    {
      return decode("������");
    }

};

#endif

/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2010 by Dimitri van Heesch.
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

#ifndef TRANSLATOR_KR_H
#define TRANSLATOR_KR_H


/* Korean translators
 * doxygen-svn
 *   * fly1004@gmail.com
 * doxygen-1.5.3
 *   * Astromaker(http://ngps.net/)
 *   * gpgiki(http://www.gpgstudy.com/gpgiki/)
 * doxygen-1.2.11
 *   * ryk */

/*! 
 When defining a translator class for the new language, follow
 the description in the documentation.  One of the steps says
 that you should copy the translator_en.h (this) file to your
 translator_xx.h new file.  Your new language should use the
 Translator class as the base class.  This means that you need to
 implement exactly the same (pure virtual) methods as the
 TranslatorEnglish does.  Because of this, it is a good idea to
 start with the copy of TranslatorEnglish and replace the strings
 one by one.

 It is not necessary to include "translator.h" or
 "translator_adapter.h" here.  The files are included in the
 language.cpp correctly.  Not including any of the mentioned
 files frees the maintainer from thinking about whether the
 first, the second, or both files should be included or not, and
 why.  This holds namely for localized translators because their
 base class is changed occasionaly to adapter classes when the
 Translator class changes the interface, or back to the
 Translator class (by the local maintainer) when the localized
 translator is made up-to-date again.
*/
class TranslatorKorean : public TranslatorAdapter_1_6_3
{
  protected:
    friend class TranslatorAdapterBase;
    virtual ~TranslatorKorean() {}

  public:

    // --- Language control methods -------------------
    
    /*! Used for identification of the language. The identification 
     * should not be translated. It should be replaced by the name 
     * of the language in English using lower-case characters only
     * (e.g. "czech", "japanese", "russian", etc.). It should be equal to 
     * the identification used in language.cpp.
     */
    virtual QCString idLanguage()
    { return "korean"; }
    
    /*! Used to get the LaTeX command(s) for the language support. 
     *  This method should return string with commands that switch
     *  LaTeX to the desired language.  For example 
     *  <pre>"\\usepackage[german]{babel}\n"
     *  </pre>
     *  or
     *  <pre>"\\usepackage{polski}\n"
     *  "\\usepackage[latin2]{inputenc}\n"
     *  "\\usepackage[T1]{fontenc}\n"
     *  </pre>
     * 
     * The English LaTeX does not use such commands.  Because of this
     * the empty string is returned in this implementation.
     */
    virtual QCString latexLanguageSupportCommand()
    {
      // I'm not sure what this should be.
      // When I figure it out, I'll update this.
      // see http://www.ktug.or.kr/jsboard/read.php?table=operate&no=4422&page=1
      return "\\usepackage{hfont}\n";
    }

    /*! return the language charset. This will be used for the HTML output */
    virtual QCString idLanguageCharset()
    {
      return "euc-kr";
    }

    // --- Language translation methods -------------------

    /*! used in the compound documentation before a list of related functions. */
    virtual QCString trRelatedFunctions()
    { return "���õ� �Լ���"; }

    /*! subscript for the related functions. */
    virtual QCString trRelatedSubscript()
    { return "(������ ��� �Լ����� �ƴմϴ�. �����Ͻʽÿ�.)"; }

    /*! header that is put before the detailed description of files, classes and namespaces. */
    virtual QCString trDetailedDescription()
    { return "���� ����"; }

    /*! header that is put before the list of typedefs. */
    virtual QCString trMemberTypedefDocumentation()
    { return "��� Ÿ������ ����ȭ"; }
    
    /*! header that is put before the list of enumerations. */
    virtual QCString trMemberEnumerationDocumentation()
    { return "��� ������ ����ȭ"; }
    
    /*! header that is put before the list of member functions. */
    virtual QCString trMemberFunctionDocumentation()
    { return "��� �Լ� ����ȭ"; }
    
    /*! header that is put before the list of member attributes. */
    virtual QCString trMemberDataDocumentation()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
          return "�ʵ� ����ȭ";
      }
      else
      {
          return "��� ����Ÿ ����ȭ";
      }
    }

    /*! this is the text of a link put after brief descriptions. */
    virtual QCString trMore() 
    { return "�� �ڼ��� ..."; }

    /*! put in the class documentation */
    virtual QCString trListOfAllMembers()
    { return "��� ��� ���"; }

    /*! used as the title of the "list of all members" page of a class */
    virtual QCString trMemberList()
    { return "��� ���"; }

    /*! this is the first part of a sentence that is followed by a class name */
    virtual QCString trThisIsTheListOfAllMembers()
    { return "������ ���� ��� ����� ����Դϴ� : "; }

    /*! this is the remainder of the sentence after the class name */
    virtual QCString trIncludingInheritedMembers()
    { return " (��� ��ӵ� ����鵵 �����մϴ�.)"; }
    
    /*! this is put at the author sections at the bottom of man pages.
     *  parameter s is name of the project name.
     */
    virtual QCString trGeneratedAutomatically(const char *s)
    { QCString result="�ҽ� �ڵ�κ��� ";
      if (s) result+=s+(QCString)"�� ���� ";
      result+="Doxygen�� ���� �ڵ����� ������."; 
      return result;
    }

    /*! put after an enum name in the list of all members */
    virtual QCString trEnumName()
    { return "������ �̸�"; }
    
    /*! put after an enum value in the list of all members */
    virtual QCString trEnumValue()
    { return "������ ��"; }
    
    /*! put after an undocumented member in the list of all members */
    virtual QCString trDefinedIn()
    { return "�������� ���ǵ� :"; }

    // quick reference sections

    /*! This is put above each page as a link to the list of all groups of 
     *  compounds or files (see the \\group command).
     */
    virtual QCString trModules()
    { return "���"; }
    
    /*! This is put above each page as a link to the class hierarchy */
    virtual QCString trClassHierarchy()
    { return "Ŭ���� ���뵵"; }
    
    /*! This is put above each page as a link to the list of annotated classes */
    virtual QCString trCompoundList()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����Ÿ ����";
      }
      else
      {
        return "Ŭ���� ���"; 
      }
    }
    
    /*! This is put above each page as a link to the list of documented files */
    virtual QCString trFileList()
    { return "���� ���"; }

    /*! This is put above each page as a link to all members of compounds. */
    virtual QCString trCompoundMembers()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����Ÿ �ʵ�"; 
      }
      else
      {
        return "Ŭ���� ���"; 
      }
    }

    /*! This is put above each page as a link to all members of files. */
    virtual QCString trFileMembers()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����"; 
      }
      else
      {
        return "���� ���"; 
      }
    }

    /*! This is put above each page as a link to all related pages. */
    virtual QCString trRelatedPages()
    { return "���õ� ������"; }

    /*! This is put above each page as a link to all examples. */
    virtual QCString trExamples()
    { return "����"; }

    /*! This is put above each page as a link to the search engine. */
    virtual QCString trSearch()
    { return "�˻�"; }

    /*! This is an introduction to the class hierarchy. */
    virtual QCString trClassHierarchyDescription()
    { return "�� ��� ����� �������� ������ ���ĺ������� �뷫������ ���ĵǾ��ֽ��ϴ�.:";
    }

    /*! This is an introduction to the list with all files. */
    virtual QCString trFileListDescription(bool extractAll)
    {
      QCString result="������ ";
      if (!extractAll) result+="����ȭ�� ";
      result+="��� ���Ͽ� ���� ����Դϴ�. (������ ������ �����ݴϴ�) :";
      return result;
    }

    /*! This is an introduction to the annotated compound list. */
    virtual QCString trCompoundListDescription()
    { 
      
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "������ ����Ÿ �������Դϴ�. (������ ������ �����ݴϴ�) :"; 
      }
      else
      {
        return "������ Ŭ����, ����ü, ����ü �׸��� �������̽����Դϴ�. "
               "(������ ������ �����ݴϴ�) :"; 
      }
    }

    /*! This is an introduction to the page with all class members. */
    virtual QCString trCompoundMembersDescription(bool extractAll)
    {
      QCString result="������ ";
      if (!extractAll)
      {
        result+="����ȭ�� ";
      }
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+="��� ����ü�� ����ü�� �ʵ��";
      }
      else
      {
        result+="��� Ŭ���� �����";
      }
      result+="�� ����Դϴ�. ";

      if (!extractAll) 
      {
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
        {
          result+="�� �ʵ���� �ش� �ʵ忡 ���� ����ü�� ����ü�� "
		  "����ȭ �������� ��ũ�� ������ �ֽ��ϴ�. :";
        }
        else
        {
          result+="�� ������� �ش� ����� ���� Ŭ������ ����ȭ �������� "
		  "��ũ�� ������ �ֽ��ϴ�. :";
        }
      }
      else 
      {
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
        {
          result+="�� �ʵ���� �ش� �ʵ尡 ���� �ִ� ����ü�� ����ü�� "
		  "���� ��ũ�� ������ �ֽ��ϴ�. :";
        }
        else
        {
          result+="�� ������� �ش� ����� ���� �ִ� Ŭ������ ���� "
		  "��ũ�� ������ �ֽ��ϴ�. :";
        }
      }
      return result;
    }

    /*! This is an introduction to the page with all file members. */
    virtual QCString trFileMembersDescription(bool extractAll)
    {
      QCString result="������ ";
      if (!extractAll) result+="����ȭ��  ";
      
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+="��� �Լ�, ����, ��ũ��, ������, Ÿ�����ǵ�";
      }
      else
      {
        result+="���� �����";
      }
      result+="�� ����Դϴ�. ";

      result+="�� �׸��� ";
      if (extractAll) 
        result+="�׵��� ���� ���� �������� ��ũ�� ������ �ֽ��ϴ�. :";
      else 
        result+="�׵鿡 ���� ����ȭ �������� ��ũ�� ������ �ֽ��ϴ�. :";
      return result;
    }

    /*! This is an introduction to the page with the list of all examples */
    virtual QCString trExamplesDescription()
    { return "������ ��� �������� ����Դϴ�.:"; }

    /*! This is an introduction to the page with the list of related pages */
    virtual QCString trRelatedPagesDescription()
    { return "������ ���õ� ��� ����ȭ ���������� ����Դϴ�.:"; }

    /*! This is an introduction to the page with the list of class/file groups */
    virtual QCString trModulesDescription()
    { return "������ ��� ������ ����Դϴ�.:"; }

    // index titles (the project name is prepended for these) 

    /*! This is used in HTML as the title of index.html. */
    virtual QCString trDocumentation()
    { return "����ȭ"; }

    /*! This is used in LaTeX as the title of the chapter with the 
     * index of all groups.
     */
    virtual QCString trModuleIndex()
    { return "��� ����"; }

    /*! This is used in LaTeX as the title of the chapter with the 
     * class hierarchy.
     */
    virtual QCString trHierarchicalIndex()
    { return "���뵵 ����"; }

    /*! This is used in LaTeX as the title of the chapter with the 
     * annotated compound index.
     */
    virtual QCString trCompoundIndex()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      { 
        return "����Ÿ ���� ����";
      }
      else
      {
        return "Ŭ���� ����"; 
      }
    }

    /*! This is used in LaTeX as the title of the chapter with the
     * list of all files.
     */
    virtual QCString trFileIndex() 
    { return "���� ����"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all groups.
     */
    virtual QCString trModuleDocumentation()
    { return "��� ����ȭ"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all classes, structs and unions.
     */
    virtual QCString trClassDocumentation()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����Ÿ ���� ����ȭ"; 
      }
      else
      {
        return "Ŭ���� ����ȭ"; 
      }
    }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all files.
     */
    virtual QCString trFileDocumentation()
    { return "���� ����ȭ"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all examples.
     */
    virtual QCString trExampleDocumentation()
    { return "���� ����ȭ"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all related pages.
     */
    virtual QCString trPageDocumentation()
    { return "������ ����ȭ"; }

    /*! This is used in LaTeX as the title of the document */
    virtual QCString trReferenceManual()
    { return "���� �Ŵ���"; }
    
    /*! This is used in the documentation of a file as a header before the 
     *  list of defines
     */
    virtual QCString trDefines()
    { return "��ũ��"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of function prototypes
     */
    virtual QCString trFuncProtos()
    { return "�Լ� ����"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of typedefs
     */
    virtual QCString trTypedefs()
    { return "Ÿ������"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of enumerations
     */
    virtual QCString trEnumerations()
    { return "������ Ÿ��"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) functions
     */
    virtual QCString trFunctions()
    { return "�Լ�"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) variables
     */
    virtual QCString trVariables()
    { return "����"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) variables
     */
    virtual QCString trEnumerationValues()
    { return "������ ���"; }
    
    /*! This is used in the documentation of a file before the list of
     *  documentation blocks for defines
     */
    virtual QCString trDefineDocumentation()
    { return "��ũ�� ����ȭ"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for function prototypes
     */
    virtual QCString trFunctionPrototypeDocumentation()
    { return "�Լ� ���� ����ȭ"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for typedefs
     */
    virtual QCString trTypedefDocumentation()
    { return "Ÿ������ ����ȭ"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for enumeration types
     */
    virtual QCString trEnumerationTypeDocumentation()
    { return "������ Ÿ�� ����ȭ"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for functions
     */
    virtual QCString trFunctionDocumentation()
    { return "�Լ� ����ȭ"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for variables
     */
    virtual QCString trVariableDocumentation()
    { return "���� ����ȭ"; }

    /*! This is used in the documentation of a file/namespace/group before 
     *  the list of links to documented compounds
     */
    virtual QCString trCompounds()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����Ÿ ����"; 
      }
      else
      {
        return "Ŭ����"; 
      }
    }

    /*! This is used in the standard footer of each page and indicates when 
     *  the page was generated 
     */
    virtual QCString trGeneratedAt(const char *date,const char *projName)
    { 
      QCString result=(QCString)"�����ð� : "+date;
      if (projName) result+=(QCString)", ������Ʈ�� : "+projName;
      result+=(QCString)", ������ : ";
      return result;
    }
    /*! This is part of the sentence used in the standard footer of each page.
     */
    virtual QCString trWrittenBy()
    {
      return "�ۼ��� : ";
    }

    /*! this text is put before a class diagram */
    virtual QCString trClassDiagram(const char *clName)
    {
      return (QCString)clName+"�� ���� ��� ���̾�׷� : ";
    }
    
    /*! this text is generated when the \\internal command is used. */
    virtual QCString trForInternalUseOnly()
    { return "�����������θ� ����ϱ� ����."; }

    /*! this text is generated when the \\warning command is used. */
    virtual QCString trWarning()
    { return "���"; }

    /*! this text is generated when the \\version command is used. */
    virtual QCString trVersion()
    { return "����"; }

    /*! this text is generated when the \\date command is used. */
    virtual QCString trDate()
    { return "��¥"; }

    /*! this text is generated when the \\return command is used. */
    virtual QCString trReturns()
    { return "��ȯ��"; }

    /*! this text is generated when the \\sa command is used. */
    virtual QCString trSeeAlso()
    { return "����"; }

    /*! this text is generated when the \\param command is used. */
    virtual QCString trParameters()
    { return "�Ű�����"; }

    /*! this text is generated when the \\exception command is used. */
    virtual QCString trExceptions()
    { return "����"; }
    
    /*! this text is used in the title page of a LaTeX document. */
    virtual QCString trGeneratedBy()
    { return "������ ���� ������ : "; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990307
//////////////////////////////////////////////////////////////////////////
    
    /*! used as the title of page containing all the index of all namespaces. */
    virtual QCString trNamespaceList()
    { return "���ӽ����̽� ���"; }

    /*! used as an introduction to the namespace list */
    virtual QCString trNamespaceListDescription(bool extractAll)
    {
      QCString result="������ ";
      if (!extractAll) result+="����ȭ�� ";
      result+="��� ���ӽ����̽��� ���� ����Դϴ�. (������ ������ �����ݴϴ�) :";
      return result;
    }

    /*! used in the class documentation as a header before the list of all
     *  friends of a class
     */
    virtual QCString trFriends()
    { return "Friends"; }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////
    
    /*! used in the class documentation as a header before the list of all
     * related classes 
     */
    virtual QCString trRelatedFunctionDocumentation()
    { return "Friend, �׸��� ���õ� �Լ� ����ȭ"; }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of the HTML page of a class/struct/union */
    virtual QCString trCompoundReference(const char *clName,
                                    ClassDef::CompoundType compType,
                                    bool isTemplate)
    {
      QCString result=(QCString)clName;
      switch(compType)
      {
        case ClassDef::Class:      result+=" Ŭ����"; break;
        case ClassDef::Struct:     result+=" ����ü"; break;
        case ClassDef::Union:      result+=" ����ü"; break;
        case ClassDef::Interface:  result+=" �������̽�"; break;
        case ClassDef::Protocol:   result+=" ��������"; break;
        case ClassDef::Category:   result+=" ī�װ�"; break;
        case ClassDef::Exception:  result+=" ����"; break;
      }
      if (isTemplate) result+=" ���ø�";
      result+=" ����";
      return result;
    }

    /*! used as the title of the HTML page of a file */
    virtual QCString trFileReference(const char *fileName)
    {
      QCString result=fileName;
      result+=" ���� ����";
      return result;
    }

    /*! used as the title of the HTML page of a namespace */
    virtual QCString trNamespaceReference(const char *namespaceName)
    {
      QCString result=namespaceName;
      result+=" ���ӽ����̽� ����";
      return result;
    }
    
    virtual QCString trPublicMembers()
    { return "Public ��� �Լ�"; }
    virtual QCString trPublicSlots()
    { return "Public Slots"; }
    virtual QCString trSignals()
    { return "Signals"; }
    virtual QCString trStaticPublicMembers()
    { return "���� Public ��� �Լ�"; }
    virtual QCString trProtectedMembers()
    { return "Protected ��� �Լ�"; }
    virtual QCString trProtectedSlots()
    { return "Protected Slots"; }
    virtual QCString trStaticProtectedMembers()
    { return "���� Protected ��� �Լ�"; }
    virtual QCString trPrivateMembers()
    { return "Private ��� �Լ�"; }
    virtual QCString trPrivateSlots()
    { return "Private Slots"; }
    virtual QCString trStaticPrivateMembers()
    { return "���� Private ��� �Լ�"; }
    
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
            result+=", ";
          else                // the fore last entry
            result+=", ";
        }
      }
      return result; 
    }
    
    /*! used in class documentation to produce a list of base classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritsList(int numEntries)
    {
      return trWriteList(numEntries)+"��(��) ����߽��ϴ�.";
    }

    /*! used in class documentation to produce a list of super classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritedByList(int numEntries)
    {
      return trWriteList(numEntries)+"�� ���� ��ӵǾ����ϴ�.";
    }

    /*! used in member documentation blocks to produce a list of 
     *  members that are hidden by this one.
     */
    virtual QCString trReimplementedFromList(int numEntries)
    {
      return trWriteList(numEntries)+"(��)�κ��� �籸���Ǿ����ϴ�.";
    }

    /*! used in member documentation blocks to produce a list of
     *  all member that overwrite the implementation of this member.
     */
    virtual QCString trReimplementedInList(int numEntries)
    {
      return trWriteList(numEntries)+"���� �籸���Ǿ����ϴ�.";
    }

    /*! This is put above each page as a link to all members of namespaces. */
    virtual QCString trNamespaceMembers()
    { return "���ӽ����̽� ���"; }

    /*! This is an introduction to the page with all namespace members */
    virtual QCString trNamespaceMemberDescription(bool extractAll)
    { 
      QCString result="������ ";
      if (!extractAll) result+="����ȭ�� ";
      result+="��� ���ӽ����̽� ������� ����Դϴ�. ";
      if (extractAll) 
        result+="�� ������� �ش� ����� ���ӽ����̽� ����ȭ �������� ��ũ�� ������ �ֽ��ϴ�. :";
      else 
        result+="�� ������� �ش� ����� ���� ���ӽ����̽� �������� ��ũ�� ������ �ֽ��ϴ�. :";
      return result;
    }
    /*! This is used in LaTeX as the title of the chapter with the 
     *  index of all namespaces.
     */
    virtual QCString trNamespaceIndex()
    { return "���ӽ����̽� ����"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all namespaces.
     */
    virtual QCString trNamespaceDocumentation()
    { return "���ӽ����̽� ����ȭ"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

    /*! This is used in the documentation before the list of all
     *  namespaces in a file.
     */
    virtual QCString trNamespaces()
    { return "���ӽ����̽�"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990728
//////////////////////////////////////////////////////////////////////////

    /*! This is put at the bottom of a class documentation page and is
     *  followed by a list of files that were used to generate the page.
     */
    virtual QCString trGeneratedFromFiles(ClassDef::CompoundType compType,
        bool single)
    { // here s is one of " Class", " Struct" or " Union"
      // single is true implies a single file
      QCString result=(QCString)"�� ";
      switch(compType)
      {
        case ClassDef::Class:      result+="Ŭ����"; break;
        case ClassDef::Struct:     result+="����ü"; break;
        case ClassDef::Union:      result+="����ü"; break;
        case ClassDef::Interface:  result+="�������̽�"; break;
        case ClassDef::Protocol:   result+="��������"; break;
        case ClassDef::Category:   result+="ī�װ�"; break;
        case ClassDef::Exception:  result+="����"; break;
      }
      result+="�� ���� ����ȭ �������� ������ ����";
      if (!single) result+="��";
      result+="�κ��� �����Ǿ����ϴ�.:";
      return result;
    }

    /*! This is in the (quick) index as a link to the alphabetical compound
     * list.
     */
    virtual QCString trAlphabeticalList()
    { return "���ĺ��� ���"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the heading text for the retval command. */
    virtual QCString trReturnValues()
    { return "��ȯ��"; }

    /*! This is in the (quick) index as a link to the main page (index.html)
     */
    virtual QCString trMainPage()
    { return "���� ������"; }

    /*! This is used in references to page that are put in the LaTeX 
     *  documentation. It should be an abbreviation of the word page.
     */
    virtual QCString trPageAbbreviation()
    { return "������"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991003
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDefinedAtLineInSourceFile()
    {
      return "@1 ������ @0 ��° ���ο��� ���ǵǾ����ϴ�.";
    }
    virtual QCString trDefinedInSourceFile()
    {
      return "@0 ���Ͽ��� ���ǵǾ����ϴ�.";
    }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991205
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDeprecated()
    {
      return "�߸��� �ڵ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

    /*! this text is put before a collaboration diagram */
    virtual QCString trCollaborationDiagram(const char *clName)
    {
      return (QCString)clName+"�� ���� ���� ���̾�׷�:";
    }
    /*! this text is put before an include dependency graph */
    virtual QCString trInclDepGraph(const char *fName)
    {
      return (QCString)fName+"�� ���� include ���� �׷���";
    }
    /*! header that is put before the list of constructor/destructors. */
    virtual QCString trConstructorDocumentation()
    {
      return "������ & �Ҹ��� ����ȭ";
    }
    /*! Used in the file documentation to point to the corresponding sources. */
    virtual QCString trGotoSourceCode()
    {
      return "�� ������ �ҽ� �ڵ� �������� ����";
    }
    /*! Used in the file sources to point to the corresponding documentation. */
    virtual QCString trGotoDocumentation()
    {
      return "�� ������ ����ȭ �������� ����";
    }
    /*! Text for the \\pre command */
    virtual QCString trPrecondition()
    {
      return "��������";
    }
    /*! Text for the \\post command */
    virtual QCString trPostcondition()
    {
      return "�Ĺ�����";
    }
    /*! Text for the \\invariant command */
    virtual QCString trInvariant()
    {
      return "������ �ʴ�";
    }
    /*! Text shown before a multi-line variable/enum initialization */
    virtual QCString trInitialValue()
    {
      return "�ʱⰪ:";
    }
    /*! Text used the source code in the file index */
    virtual QCString trCode()
    {
      return "�ڵ�";
    }
    virtual QCString trGraphicalHierarchy()
    {
      return "�׷������� Ŭ���� ���뵵";
    }
    virtual QCString trGotoGraphicalHierarchy()
    {
      return "�׷������� Ŭ���� ���뵵 �������� ����";
    }
    virtual QCString trGotoTextualHierarchy()
    {
      return "�ؽ�Ʈ ������ Ŭ���� ���뵵 �������� ����";
    }
    virtual QCString trPageIndex()
    {
      return "������ ����";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////
    
    virtual QCString trNote()
    {
      return "����";
    }
    virtual QCString trPublicTypes()
    {
      return "Public Ÿ��";
    }
    virtual QCString trPublicAttribs()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����Ÿ �ʵ�";
      }
      else
      {
        return "Public �Ӽ�";
      }
    }
    virtual QCString trStaticPublicAttribs()
    {
      return "���� Public �Ӽ�";
    }
    virtual QCString trProtectedTypes()
    {
      return "Protected Ÿ��";
    }
    virtual QCString trProtectedAttribs()
    {
      return "Protected �Ӽ�";
    }
    virtual QCString trStaticProtectedAttribs()
    {
      return "���� Protected �Ӽ�";
    }
    virtual QCString trPrivateTypes()
    {
      return "Private Ÿ��";
    }
    virtual QCString trPrivateAttribs()
    {
      return "Private �Ӽ�";
    }
    virtual QCString trStaticPrivateAttribs()
    {
      return "���� Private �Ӽ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a \\todo item */
    virtual QCString trTodo()
    {
      return "����";
    }
    /*! Used as the header of the todo list */
    virtual QCString trTodoList()
    {
      return "���� ���";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

    virtual QCString trReferencedBy()
    {
      return "������ ���ؼ� ������ : ";
    }
    virtual QCString trRemarks()
    {
      return "Remarks";
    }
    virtual QCString trAttention()
    {
        return "����";
    }
    virtual QCString trInclByDepGraph()
    {
      return "�� �׷����� �� ������ ��/���������� include �ϴ� ���ϵ��� �����ݴϴ�.:";
    }
    virtual QCString trSince()
    {
      return "Since";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

    /*! title of the graph legend page */
    virtual QCString trLegendTitle()
    {
      return "�׷��� ����";
    }
    /*! page explaining how the dot graph's should be interpreted 
     *  The %A in the text below are to prevent link to classes called "A".
     */
    virtual QCString trLegendDocs()
    {
      return 
        "�� �������� doxygen�� ���� ������ �׷������� �����ϴ� ����� �����մϴ�.<p>\n"
        "������ ������ �����Ͻʽÿ�.:\n"
        "\\code\n"
        "/*! �����Ǿ��� ������ ������ �ʴ� Ŭ���� */\n"
        "class Invisible { };\n\n"
        "/*! Truncated Ŭ����, ��Ӱ��谡 ������ */\n"
        "class Truncated : public Invisible { };\n\n"
        "/* doxygen �ּ��� ���ؼ� ����ȭ���� �ʴ� Ŭ���� */\n"
        "class Undocumented { };\n\n"
        "/*! public ����� ���ؼ� ��ӵ� Ŭ���� */\n"
        "class PublicBase : public Truncated { };\n\n"
        "/*! ���ø� Ŭ���� */\n"
        "template<class T> class Templ { };\n\n"
        "/*! protected ����� ���ؼ� ��ӵ� Ŭ���� */\n"
        "class ProtectedBase { };\n\n"
        "/*! private ����� ���ؼ� ��ӵ� Ŭ���� */\n"
        "class PrivateBase { };\n\n"
        "/*! ��ӵǾ��� Ŭ������ ���� (�����) ���Ǿ����� Ŭ���� */\n"
        "class Used { };\n\n"
        "/*! �ٸ� Ŭ�������� ����ϴ� ���� Ŭ���� */\n"
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
        "������ ���� �׷����� ��µ� ���Դϴ�. :"
        "<p><center><img alt=\"\" src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
        "<p>\n"
        "�� �׷����� �ڽ����� ������ ���� �ǹ̸� �����ϴ�. :\n"
        "<ul>\n"
        "<li>%A ȸ������ ä���� �ڽ��� �� �׷����� ������ �� ����ü�� Ŭ������ �ǹ��մϴ�.\n"
        "<li>%A ������ �׵θ��� �ڽ��� ����ȭ�� ����ü�� Ŭ������ �ǹ��մϴ�.\n"
        "<li>%A ȸ�� �׵θ��� �ڽ��� ����ȭ���� ���� ����ü�� Ŭ������ �ǹ��մϴ�.\n"
        "<li>%A ������ �׵θ��� �ڽ��� ��� ����̳� ���԰��谡 �������� �ʴ� "
	"����ü�� Ŭ������ �ǹ��մϴ�."
        "%A ���� �׷����� ������ ��賻�� ���� ������, �׷����� �߷����ϴ�.\n"
        "</ul>\n"
        "ȭ��ǥ���� ������ ���� �ǹ̸� �����ϴ�. :\n"
        "<ul>\n"
        "<li>%A ��ο� �Ķ��� ȭ��ǥ�� �� Ŭ������ ���� public ����� ������ �ǹ��մϴ�.\n"
        "<li>%A ��ο� ���λ� ȭ��ǥ�� protected ����� ������ �ǹ��մϴ�.\n"
        "<li>%A ��ο� ������ ȭ��ǥ�� private ����� ������ �ǹ��մϴ�.\n"
        "<li>%A ����� ���� ȭ��ǥ�� �ٸ� Ŭ������ ���� ���Եǰų� ���Ǿ����� �ǹ��մϴ�. "
	"ȭ��ǥ�� ���� ȭ��ǥ�� ����Ű�� Ŭ������ ����ü�� �����ϴ� ������(��)���� �ٽ��ϴ�.\n"
        "<li>%A ����� ���� ȭ��ǥ�� ���ø� �ν��Ͻ��� ������ Ŭ������ ���� ���踦 �ǹ��մϴ�. "
	"ȭ��ǥ�� ���� �ν��Ͻ��� ���ø� �Ķ���ͷ� �ٽ��ϴ�.\n"
        "</ul>\n";
    }
    /*! text for the link to the legend page */
    virtual QCString trLegend()
    {
      return "����";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a test item */
    virtual QCString trTest()
    {
      return "�׽�Ʈ";
    }
    /*! Used as the header of the test list */
    virtual QCString trTestList()
    {
      return "�׽�Ʈ ���";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.1
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for KDE-2 IDL methods */
    virtual QCString trDCOPMethods()
    {
      return "DCOP ��� �Լ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.2
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for IDL properties */
    virtual QCString trProperties()
    {
      return "�Ӽ�";
    }
    /*! Used as a section header for IDL property documentation */
    virtual QCString trPropertyDocumentation()
    {
      return "�Ӽ� ����ȭ";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

    /*! Used for Java classes in the summary section of Java packages */
    virtual QCString trClasses()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "����Ÿ ����";
      }
      else
      {
        return "Ŭ����";
      }
    }
    /*! Used as the title of a Java package */
    virtual QCString trPackage(const char *name)
    {
      return name+(QCString)" ��Ű��";
    }
    /*! Title of the package index page */
    virtual QCString trPackageList()
    {
      return "��Ű�� ���";
    }
    /*! The description of the package index page */
    virtual QCString trPackageListDescription()
    {
      return "������ ��Ű�����Դϴ�. (�������� ������ ������ �����ݴϴ�) :";
    }
    /*! The link name in the Quick links header for each page */
    virtual QCString trPackages()
    {
      return "��Ű��";
    }
    /*! Text shown before a multi-line define */
    virtual QCString trDefineValue()
    {
      return "��:";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.2.5
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a \\bug item */
    virtual QCString trBug()
    {
      return "����";
    }
    /*! Used as the header of the bug list */
    virtual QCString trBugList()
    {
      return "���� ���";
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
      return "949";
    }
    

    /*! Used as ansicpg for RTF fcharset 
     *  \see trRTFansicp() for a table of possible values.
     */
    virtual QCString trRTFCharSet()
    {
      return "129";
    }

    /*! Used as header RTF general index */
    virtual QCString trRTFGeneralIndex()
    {
      return "����";
    }
   
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trClass(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "Ŭ����" : "Ŭ����"));
      if (!singular)  result+="��";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trFile(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "����" : "����"));
      if (!singular)  result+="��";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trNamespace(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "���ӽ����̽�" : "���ӽ����̽�"));
      if (!singular)  result+="��";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGroup(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "�׷�" : "�׷�"));
      if (!singular)  result+="��";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trPage(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "������" : "������"));
      if (!singular)  result+="��";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trMember(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "���" : "���"));
      if (!singular)  result+="��";
      return result; 
    }
   
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGlobal(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "����" : "����"));
      if (!singular)  result+="";
      return result; 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

    /*! This text is generated when the \\author command is used and
     *  for the author section in man pages. */
    virtual QCString trAuthor(bool first_capital, bool singular)
    {                                                                         
      QCString result((first_capital ? "�ۼ���" : "�ۼ���"));
      if (!singular)  result+="��";
      return result; 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

    /*! This text is put before the list of members referenced by a member
     */
    virtual QCString trReferences()
    {
      return "������ ������ : ";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

    /*! used in member documentation blocks to produce a list of 
     *  members that are implemented by this one.
     */
    virtual QCString trImplementedFromList(int numEntries)
    {
      return trWriteList(numEntries)+"�� ����.";
    }

    /*! used in member documentation blocks to produce a list of
     *  all members that implement this abstract member.
     */
    virtual QCString trImplementedInList(int numEntries)
    {
      return trWriteList(numEntries)+"���� �����Ǿ����ϴ�.";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

    /*! used in RTF documentation as a heading for the Table
     *  of Contents.
     */
    virtual QCString trRTFTableOfContents()
    {
      return "����";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

    /*! Used as the header of the list of item that have been 
     *  flagged deprecated 
     */
    virtual QCString trDeprecatedList()
    {
      return "�߸��� �ڵ� ���";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.18
//////////////////////////////////////////////////////////////////////////

    /*! Used as a header for declaration section of the events found in 
     * a C# program
     */
    virtual QCString trEvents()
    {
      return "�̺�Ʈ";
    }
    /*! Header used for the documentation section of a class' events. */
    virtual QCString trEventDocumentation()
    {
      return "�̺�Ʈ ����ȭ";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a heading for a list of Java class types with package scope.
     */
    virtual QCString trPackageTypes()
    { 
      return "��Ű�� Ÿ��";
    }
    /*! Used as a heading for a list of Java class functions with package 
     * scope. 
     */
    virtual QCString trPackageMembers()
    { 
      return "��Ű�� �Լ�";
    }
    /*! Used as a heading for a list of static Java class functions with 
     *  package scope.
     */
    virtual QCString trStaticPackageMembers()
    { 
      return "���� ��Ű�� �Լ�";
    }
    /*! Used as a heading for a list of Java class variables with package 
     * scope.
     */
    virtual QCString trPackageAttribs()
    { 
      return "��Ű�� �Ӽ�";
    }
    /*! Used as a heading for a list of static Java class variables with 
     * package scope.
     */
    virtual QCString trStaticPackageAttribs()
    { 
      return "���� ��Ű�� �Ӽ�";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.3.1
//////////////////////////////////////////////////////////////////////////

    /*! Used in the quick index of a class/file/namespace member list page 
     *  to link to the unfiltered list of all members.
     */
    virtual QCString trAll()
    {
      return "���";
    }
    /*! Put in front of the call graph for a function. */
    virtual QCString trCallGraph()
    {
      return "�� �Լ� ���ο��� ȣ���ϴ� �Լ��鿡 ���� �׷����Դϴ�.:";
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
      return "�˻�";
    }
    /*! This string is used as the title for the page listing the search
     *  results.
     */
    virtual QCString trSearchResultsTitle()
    {
      return "�˻� ���";
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
        return "�˼��մϴ�. ���ǿ� ��ġ�ϴ� ������ �����ϴ�.";
      }
      else if (numDocuments==1)
      {
        return "���ǿ� ��ġ�ϴ� <b>1</b> ���� ������ ã�ҽ��ϴ�.";
      }
      else 
      {
        return "���ǿ� ��ġ�ϴ� <b>$num</b> ���� ������ ã�ҽ��ϴ�. "
               "���� ���� ��ġ�ϴ� ������ ���� ���� �����ݴϴ�.";
      }
    }
    /*! This string is put before the list of matched words, for each search 
     *  result. What follows is the list of words that matched the query.
     */
    virtual QCString trSearchMatches()
    {
      return "���:";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.8
//////////////////////////////////////////////////////////////////////////

    /*! This is used in HTML as the title of page with source code for file filename
     */
    virtual QCString trSourceFile(QCString& filename)
    {
      return filename + " �ҽ� ����";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.9
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the name of the chapter containing the directory
     *  hierarchy.
     */
    virtual QCString trDirIndex()
    { return "���丮 ���뵵"; }

    /*! This is used as the name of the chapter containing the documentation
     *  of the directories.
     */
    virtual QCString trDirDocumentation()
    { return "���丮 ����ȭ"; }

    /*! This is used as the title of the directory index and also in the
     *  Quick links of an HTML page, to link to the directory hierarchy.
     */
    virtual QCString trDirectories()
    { return "���丮"; }

    /*! This returns a sentences that introduces the directory hierarchy. 
     *  and the fact that it is sorted alphabetically per level
     */
    virtual QCString trDirDescription()
    { return "�� ���丮 ����� �������� ������, (�뷫������) ���ĺ������� ���ĵǾ��ֽ��ϴ�.:";
    }

    /*! This returns the title of a directory page. The name of the
     *  directory is passed via \a dirName.
     */
    virtual QCString trDirReference(const char *dirName)
    { QCString result=dirName; result+=" ���丮 ����"; return result; }

    /*! This returns the word directory with or without starting capital
     *  (\a first_capital) and in sigular or plural form (\a singular).
     */
    virtual QCString trDir(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "���丮" : "���丮"));
      if (singular) result+=""; else result+="��";
      return result; 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.4.1
//////////////////////////////////////////////////////////////////////////

    /*! This text is added to the documentation when the \\overload command
     *  is used for a overloaded function.
     */
    virtual QCString trOverloadText()
    {
       return "�� �Լ��� ���Ǹ� �����ϱ� ���� �����ε�� ��� �Լ��Դϴ�. "
              "���� �Լ��� Ʋ�� ���� ���� �޾Ƶ��̴� �ƱԸ�Ʈ(argument)�� �ٸ��ٴ� ���Դϴ�.";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.4.6
//////////////////////////////////////////////////////////////////////////

    /*! This is used to introduce a caller (or called-by) graph */
    virtual QCString trCallerGraph()
    {
      return "�� �Լ��� ȣ���ϴ� �Լ��鿡 ���� �׷����Դϴ�.:";
    }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for enumeration values
     */
    virtual QCString trEnumerationValueDocumentation()
    { return "������ ����ȭ"; }

//////////////////////////////////////////////////////////////////////////
// new since 1.5.4 (mainly for Fortran)
//////////////////////////////////////////////////////////////////////////
    
    /*! header that is put before the list of member subprograms (Fortran). */
    virtual QCString trMemberFunctionDocumentationFortran()
    { return "��� �Լ�/�����ƾ ����ȭ"; }

    /*! This is put above each page as a link to the list of annotated data types (Fortran). */    
    virtual QCString trCompoundListFortran()
    { return "����Ÿ Ÿ�� ���"; }

    /*! This is put above each page as a link to all members of compounds (Fortran). */
    virtual QCString trCompoundMembersFortran()
    { return "����Ÿ �ʵ�"; }

    /*! This is an introduction to the annotated compound list (Fortran). */
    virtual QCString trCompoundListDescriptionFortran()
    { return "�뷫���� ����� �Բ� ����Ÿ Ÿ�Ե��� ����Դϴ�.:"; }

    /*! This is an introduction to the page with all data types (Fortran). */
    virtual QCString trCompoundMembersDescriptionFortran(bool extractAll)
    {
      QCString result="������ ";
      if (!extractAll)
      {
        result+="����ȭ�� ";
      }
      result+="��� ����Ÿ Ÿ�� ������� ����Դϴ�. ";

      result+="�� �׸��� ";
      if (!extractAll) 
      {
         result+="�� ����� ���� ����Ÿ ���� ����ȭ �������� ��ũ�� ������ �ֽ��ϴ�.";
      }
      else 
      {
         result+="�׵��� ���� ����Ÿ Ÿ���� ��ũ�� ������ �ֽ��ϴ�. :";
      }
      return result;
    }

    /*! This is used in LaTeX as the title of the chapter with the 
     * annotated compound index (Fortran).
     */
    virtual QCString trCompoundIndexFortran()
    { return "����Ÿ Ÿ�� ����"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all data types (Fortran).
     */
    virtual QCString trTypeDocumentation()
    { return "����Ÿ Ÿ�� ����ȭ"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) subprograms (Fortran).
     */
    virtual QCString trSubprograms()
    { return "�Լ�/�����ƾ"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for subprograms (Fortran)
     */
    virtual QCString trSubprogramDocumentation()
    { return "�Լ�/�����ƾ ����ȭ"; }

    /*! This is used in the documentation of a file/namespace/group before 
     *  the list of links to documented compounds (Fortran)
     */
     virtual QCString trDataTypes()
    { return "����Ÿ Ÿ�Ե�"; }
    
    /*! used as the title of page containing all the index of all modules (Fortran). */
    virtual QCString trModulesList()
    { return "��� ���"; }

    /*! used as an introduction to the modules list (Fortran) */
    virtual QCString trModulesListDescription(bool extractAll)
    {
      QCString result="������ ";
      if (!extractAll) result+="����ȭ�� ";
      result+="��� ��⿡ ���� ����Դϴ�. (������ ������ �����ݴϴ�) :";
      return result;
    }

    /*! used as the title of the HTML page of a module/type (Fortran) */
    virtual QCString trCompoundReferenceFortran(const char *clName,
                                    ClassDef::CompoundType compType,
                                    bool isTemplate)
    {
      QCString result=(QCString)clName;
      switch(compType)
      {
        case ClassDef::Class:      result+=" ���"; break;
        case ClassDef::Struct:     result+=" Ÿ��"; break;
        case ClassDef::Union:      result+=" ����ü"; break;
        case ClassDef::Interface:  result+=" �������̽�"; break;
        case ClassDef::Protocol:   result+=" ��������"; break;
        case ClassDef::Category:   result+=" ī�װ�"; break;
        case ClassDef::Exception:  result+=" ����"; break;
      }
      if (isTemplate) result+=" ���ø�";
      result+=" ����";
      return result;
    }
    /*! used as the title of the HTML page of a module (Fortran) */
    virtual QCString trModuleReference(const char *namespaceName)
    {
      QCString result=namespaceName;
      result+=" ��� ����";        
      return result;
    }
    
    /*! This is put above each page as a link to all members of modules. (Fortran) */
    virtual QCString trModulesMembers()
    { return "��� �����"; }

    /*! This is an introduction to the page with all modules members (Fortran) */
    virtual QCString trModulesMemberDescription(bool extractAll)
    { 
      QCString result="������ ";
      if (!extractAll) result+="����ȭ�� ";
      result+="��� ��� ����� ����Դϴ�. ";
      if (extractAll) 
      {
        result+="�� �׸��� �� ����� ��� ����ȭ �������� ��ũ�� ������ �ֽ��ϴ�. :";
      }
      else 
      {
        result+="�� �׸��� �׵��� ���� ����� ��ũ�� ������ �ֽ��ϴ�. :";
      }
      return result;
    }

    /*! This is used in LaTeX as the title of the chapter with the 
     *  index of all modules (Fortran).
     */
    virtual QCString trModulesIndex()
    { return "��� ����"; }
    
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trModule(bool first_capital, bool singular)
    {       
      QCString result((first_capital ? "���" : "���"));
      if (!singular)  result+="��";
      return result; 
    }
    /*! This is put at the bottom of a module documentation page and is
     *  followed by a list of files that were used to generate the page.
     */
    virtual QCString trGeneratedFromFilesFortran(ClassDef::CompoundType compType,
        bool single)
    { // here s is one of " Module", " Struct" or " Union"
      // single is true implies a single file
      QCString result=(QCString)"���� ����";
      if (single) result+=""; else result+="��";
      result+="�κ��� ������ ";
      result+="�� ";
      switch(compType)
      {
        case ClassDef::Class:      result+="���"; break;
        case ClassDef::Struct:     result+="Ÿ��"; break;
        case ClassDef::Union:      result+="����ü"; break;
        case ClassDef::Interface:  result+="�������̽�"; break;
        case ClassDef::Protocol:   result+="��������"; break;
        case ClassDef::Category:   result+="ī�װ�"; break;
        case ClassDef::Exception:  result+="����"; break;
      }
      result+="�� ����ȭ ������:";
      return result;
    }
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trType(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "Ÿ��" : "Ÿ��"));
      if (!singular)  result+="��";
      return result; 
    }
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trSubprogram(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "�������α׷�" : "�������α׷�"));
      if (!singular)  result+="��";
      return result; 
    }

    /*! C# Type Constraint list */
    virtual QCString trTypeConstraints()
    {
      return "Ÿ�� �����ڵ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.6.0 (mainly for the new search engine)
//////////////////////////////////////////////////////////////////////////

    /*! directory relation for \a name */
    virtual QCString trDirRelation(const char *name)
    {
      return QCString(name)+" ����";
    }

    /*! Loading message shown when loading search results */
    virtual QCString trLoading()
    {
      return "�ε���...";
    }

    /*! Label used for search results in the global namespace */
    virtual QCString trGlobalNamespace()
    {
      return "���� �̸�����";
    }

    /*! Message shown while searching */
    virtual QCString trSearching()
    {
      return "�˻���...";
    }

    /*! Text shown when no search results are found */
    virtual QCString trNoMatches()
    {
      return "��ġ�ϴ°� ����";
    }

};

#endif

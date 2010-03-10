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

#ifndef TRANSLATOR_CN_H
#define TRANSLATOR_CN_H

/*!
   If you want insert a space whenever Chinese meets English charactors, set
   CN_SPC to " ", else null.
*/
#define CN_SPC

class TranslatorChinese : public TranslatorAdapter_1_6_0
{
  public:
		/*! Used for identification of the language. The identification
		 * should not be translated. It should be replaced by the name
		 * of the language in English using lower-case characters only
		 * (e.g. "czech", "japanese", "russian", etc.). It sould be equal to
		 * the identification used in the language.cpp.
		 */
    
    virtual QCString idLanguage()
    { return "chinese"; }

    /*! Used to get the LaTeX command(s) for the language support. 
     * This method should return string with commands that switch
     * LaTeX to the desired language.  For example 
     * <pre>"\\usepackage[german]{babel}\n"
     * </pre>
     * or
     * <pre>"\\usepackage{polski}\n"
     * "\\usepackage[latin2]{inputenc}\n"
     * "\\usepackage[T1]{fontenc}\n"
     * </pre>
     * 
     * The English LaTeX does not use such commands.  Because of this
     * the empty string is returned in this implementation.
     */
    virtual QCString latexLanguageSupportCommand()
    {
      return "";
    }


		/*! return the language charset. This will be used for the HTML output */
    virtual QCString idLanguageCharset()
    { return "gb2312"; }

		/*! used in the compound documentation before a list of related functions. 
		 */
    virtual QCString trRelatedFunctions()
    { return "��غ���"; }

		/*! subscript for the related functions. */
    virtual QCString trRelatedSubscript()
    { return "��ע�⣺��Щ���ǳ�Ա��������"; }

		/*! header that is put before the detailed description of files, 
		 * classes and namespaces. 
		 */
    virtual QCString trDetailedDescription()
    { return "��ϸ����"; }

		/*! header that is put before the list of typedefs. */
    virtual QCString trMemberTypedefDocumentation()
    { return "��Ա���Ͷ����ĵ�"; }

		/*! header that is put before the list of enumerations. */
    virtual QCString trMemberEnumerationDocumentation()
    { return "��Աö�������ĵ�"; }

		/*! header that is put before the list of member function. */
    virtual QCString trMemberFunctionDocumentation()
    { return "��Ա�����ĵ�"; }

		/*! header that is put before the list of member attributes. */
    virtual QCString trMemberDataDocumentation()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) 
			{
				return "�ֶ��ĵ�"; 
			}
			else {
				return "��Ա�����ĵ�"; 
			}
		}

		/*! this is the text of a link put after brief descriptions. */
    virtual QCString trMore()
    { return "����..."; }

		/*! put in the class documention */
    virtual QCString trListOfAllMembers()
    { return "���г�Ա���б�"; }

		/*! used as the title of the "list of all members" page of a class */
    virtual QCString trMemberList()
    { return "��Ա�б�"; }

		/*! this is the first part of a sentence that is followed by a class name */
    virtual QCString trThisIsTheListOfAllMembers()
    { return "��Ա�������б���Щ��Ա����"CN_SPC; }

		/*! this is the remainder of the sentence after the class name */
    virtual QCString trIncludingInheritedMembers()
    { return "���������м̳ж����ĳ�Ա"; }

		/*! this is put at the author sections at the bottom of man pages.
		 *  parameter s is name of the project name.
		 */
    virtual QCString trGeneratedAutomatically(const char *s)
    {
			QCString result;
      if (s) result=(QCString)"Ϊ"CN_SPC+s+"��";
      result+="��"CN_SPC"Doyxgen"CN_SPC"ͨ������Դ�����Զ����ɡ�"; 
      return result;
    }

		/*! put after an enum name in the list of all members */
    virtual QCString trEnumName()
    { return "ö������"; }

		/*! put after an enum value in the list of all members */
    virtual QCString trEnumValue()
    { return "ö��ֵ"; }

		/*! put after an undocumented member in the list of all members */
    virtual QCString trDefinedIn()
    { return "������"CN_SPC; }

		// quick reference sections


		/*! This is put above each page as a link to the list of all groups of 
		 *  compounds or files (see the \\group command).
		 */
    virtual QCString trModules()
    { return "ģ��"; }

		/*! This is put above each page as a link to the class hierarchy */
 		virtual QCString trClassHierarchy()
    { return "��̳й�ϵ"; }

		/*! This is put above each page as a link to the list of annotated class */
 		virtual QCString trCompoundList()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) {
				return "���ݽṹ"; 
			}
			else {
				return "��������б�"; 
			}
		}

		/*! This is put above each page as a link to the list of documented files */
    virtual QCString trFileList()
    { return "�ļ��б�"; }

		/*! This is put above each page as a link to all members of compounds. */
    virtual QCString trCompoundMembers()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) { 
				return "�����ֶ�"; 
			}
			else {
				return "������ͳ�Ա"; 
			}
		}

		/*! This is put above each page as a link to all member of files. */
    virtual QCString trFileMembers()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) {
				return "ȫ�ֶ���"; 
			} else {
				return "�ļ���Ա"; 
			}
		}

		/*! This is put above each page as a link to all related pages. */
    virtual QCString trRelatedPages()
    { return "���ҳ��"; }

		/*! This is put above each page as a link to all examples. */
    virtual QCString trExamples()
    { return "ʾ��"; }

    virtual QCString trSearch()
    { return "����"; }

    virtual QCString trClassHierarchyDescription()
    { return "���б�������ֵ�˳������"; }

    virtual QCString trFileListDescription(bool extractAll)
    {
   		QCString result="�����г�����";
      if (!extractAll) result+="�ĵ�����";
      result+="�ļ���������Ҫ˵����";
      return result;
    }

    virtual QCString trCompoundListDescription()
    { 

			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
			{
				return "�����г��������ݽṹ��������Ҫ˵����"; 
			}
			else
			{
				return "�����г������ࡢ�ṹ�������Լ��ӿڶ��壬������Ҫ˵����"; 
			}
    }

    virtual QCString trCompoundMembersDescription(bool extractAll)
    {
   		QCString result="�����г�����";
      if (!extractAll) {
				result+="�ĵ�����";
			}
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) {
				result+="�ṹ�����ϵĳ�Ա������";
			}
			else {
				result+="���Ա������";
			}

      if (extractAll) {
				if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) {
					result+="���ڽṹ�����ϵ��ĵ������ӣ�";
				}
				else {
					result+="��������ĵ������ӣ�";
				}
			}
      else {
				if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) {
					result+="�����ṹ�����ϵ����ӣ�";
				}
				else {
					result+="����������ӣ�";
				}
			}
      return result;
    }

    virtual QCString trFileMembersDescription(bool extractAll)
    {
   		QCString result="�����г�����";
      if (!extractAll) 
				result +="�ĵ�����";

			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C")) {
				result +="�������������꣬ö�ٺ����Ͷ��壬����";
			} 
			else {
				result +="�ļ���Ա������";
			}

      if (extractAll) 
				result+="�����ļ����ĵ������ӣ�";
      else 
				result+="�����ļ������ӣ�";
      return result;
    }

    virtual QCString trExamplesDescription()
    { return "�����г�����ʾ����"; }

    virtual QCString trRelatedPagesDescription()
    { return "�����г�������ص�ҳ�棺"; }

    virtual QCString trModulesDescription()
    { return "�����г�����ģ��"; }

    virtual QCString trDocumentation()
    { return "�ĵ�"; }

    virtual QCString trModuleIndex()
    { return "ģ������"; }

    virtual QCString trHierarchicalIndex()
    { return "�̳й�ϵ����"; }

    virtual QCString trCompoundIndex()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
			{
				return "���ݽṹ����"; 
			} 
			else {
				return "�����������"; 
			}
		}

    virtual QCString trFileIndex() 
    { return "�ļ�����"; }

    virtual QCString trModuleDocumentation()
    { return "ģ���ĵ�"; }

    virtual QCString trClassDocumentation()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
			{
				return "���ݽṹ�ĵ�";
			}
			else {
				return "���ĵ�"; 
			}
		}

    virtual QCString trFileDocumentation()
    { return "�ļ��ĵ�"; }

    virtual QCString trExampleDocumentation()
    { return "ʾ���ĵ�"; }

    virtual QCString trPageDocumentation()
    { return "ҳ���ĵ�"; }

    virtual QCString trReferenceManual()
    { return "�ο��ֲ�"; }

    virtual QCString trDefines()
    { return "�궨��"; }

    virtual QCString trFuncProtos()
    { return "����ԭ��"; }

    virtual QCString trTypedefs()
    { return "���Ͷ���"; }

    virtual QCString trEnumerations()
    { return "ö��"; }

    virtual QCString trFunctions()
    { return "����"; }

    virtual QCString trVariables()
    { return "����"; }

    virtual QCString trEnumerationValues()
    { return "ö��ֵ"; }


 		virtual QCString trDefineDocumentation()
    { return "�궨���ĵ�"; }

 		virtual QCString trFunctionPrototypeDocumentation()
    { return "����ԭ���ĵ�"; }

 		virtual QCString trTypedefDocumentation()
    { return "���Ͷ����ĵ�"; }

 		virtual QCString trEnumerationTypeDocumentation()
    { return "ö�������ĵ�"; }

 		virtual QCString trFunctionDocumentation()
    { return "�����ĵ�"; }

 		virtual QCString trVariableDocumentation()
    { return "�����ĵ�"; }

 		virtual QCString trCompounds()
    { 
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
			{ 
				return "���ݽṹ";
			}
			else {
				return "�������"; 
			}
		}

 		virtual QCString trGeneratedAt(const char *date,const char *projName)
    { 
   		QCString result=(QCString)"Generated at "+date;
      if (projName) result+=(QCString)" for "+projName;
      result+=(QCString)" by";
      return result;
    }

 		virtual QCString trWrittenBy()
    {
      return "written by";
    }

 		virtual QCString trClassDiagram(const char *clName)
    {
      return (QCString)"�̳�ͼ����"CN_SPC+clName;
    }

 		virtual QCString trForInternalUseOnly()
    { return "�����ڲ�ʹ�á�"; }

 		virtual QCString trWarning()
    { return "����"; }

 		virtual QCString trVersion()
    { return "�汾"; }

 		virtual QCString trDate()
    { return "����"; }

 		virtual QCString trReturns()
    { return "����"; }

 		virtual QCString trSeeAlso()
    { return "�μ�"; }

 		virtual QCString trParameters()
    { return "����"; }

 		virtual QCString trExceptions()
    { return "�쳣"; }

 		virtual QCString trGeneratedBy()
    { return "������"; }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990307 
//////////////////////////////////////////////////////////////////////////
    
 		virtual QCString trNamespaceList()
    { return "���ֿռ��б�"; }

 		virtual QCString trNamespaceListDescription(bool extractAll)
    {
   		QCString result="�����г�����";
      if (!extractAll) result+="�ĵ�����";
      result+="���ֿռ䶨�壬������Ҫ˵����";
      return result;
    }

 		virtual QCString trFriends()
    { return "��Ԫ"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////
    
 		virtual QCString trRelatedFunctionDocumentation()
    { return "��Ԫ����غ����ĵ�"; }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

 		virtual QCString trCompoundReference(const char *clName,
                                 ClassDef::CompoundType compType,
                                 bool isTemplate)
      // used as the title of the HTML page of a class/struct/union
    {
   		QCString result=(QCString)clName;
      if (isTemplate) result+=CN_SPC"ģ��";
      switch(compType)
      {
        case ClassDef::Class:  result+="��"; break;
        case ClassDef::Struct: result+="�ṹ"; break;
        case ClassDef::Union:  result+="����"; break;
        case ClassDef::Interface:  result+="�ӿ�"; break;
        case ClassDef::Protocol:   result+="Э��"; break;
        case ClassDef::Category:   result+="����"; break;
        case ClassDef::Exception:  result+="�쳣"; break;
      }
      result+="�ο�";
      return result;
    }

 		virtual QCString trFileReference(const char *fileName)
      // used as the title of the HTML page of a file
    {
   		QCString result=fileName;
      result+=CN_SPC"�ļ��ο�"; 
      return result;
    }

 		virtual QCString trNamespaceReference(const char *namespaceName)
      // used as the title of the HTML page of a namespace
    {
   		QCString result=namespaceName;
      result+=CN_SPC"���ֿռ�ο�";
      return result;
    }
    
    // these are for the member sections of a class, struct or union 
 		virtual QCString trPublicMembers()
    { return "���г�Ա"; }

 		virtual QCString trPublicSlots()
    { return "���в�"; }

 		virtual QCString trSignals()
    { return "�ź�"; }

 		virtual QCString trStaticPublicMembers()
    { return "��̬���г�Ա"; }

 		virtual QCString trProtectedMembers()
    { return "������Ա"; }

 		virtual QCString trProtectedSlots()
    { return "������"; }

 		virtual QCString trStaticProtectedMembers()
    { return "��̬������Ա"; }
		
 		virtual QCString trPrivateMembers()
    { return "˽�г�Ա"; }
		
 		virtual QCString trPrivateSlots()
    { return "˽�в�"; }
		
 		virtual QCString trStaticPrivateMembers()
    { return "��̬˽�г�Ա"; }
		
    // end of member sections 
    
 		virtual QCString trWriteList(int numEntries)
    {
      // this function is used to produce a comma-separated list of items.
      // use generateMarker(i) to indicate where item i should be put.
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
            result+="��";
          else                // the fore last entry
            result+=CN_SPC"��"CN_SPC;
        }
      }
      return result; 
    }
    
 		virtual QCString trInheritsList(int numEntries)
      // used in class documentation to produce a list of base classes,
      // if class diagrams are disabled.
    {
      return "�̳���"CN_SPC+trWriteList(numEntries)+"��";
    }

 		virtual QCString trInheritedByList(int numEntries)
      // used in class documentation to produce a list of super classes,
      // if class diagrams are disabled.
    {
      return "��"CN_SPC+trWriteList(numEntries)+CN_SPC"�̳�.";
    }
		
 		virtual QCString trReimplementedFromList(int numEntries)
      // used in member documentation blocks to produce a list of 
      // members that are hidden by this one.
    {
      return "����"CN_SPC+trWriteList(numEntries)+"��";
    }
		
 		virtual QCString trReimplementedInList(int numEntries)
    {
      // used in member documentation blocks to produce a list of
      // all member that overwrite the implementation of this member.
      return "��"CN_SPC+trWriteList(numEntries)+CN_SPC"���ء�";
    }

 		virtual QCString trNamespaceMembers()
      // This is put above each page as a link to all members of namespaces.
    { return "���ֿռ��Ա"; }
		
 		virtual QCString trNamespaceMemberDescription(bool extractAll)
      // This is an introduction to the page with all namespace members
    { 
   		QCString result="�����г�������";
      if (!extractAll) result+="�ĵ�����";
      result+="���ֿռ��Ա������";
      if (extractAll) 
        result+="��������ĵ������ӣ�";
      else 
        result+="����������ӣ�";
      return result;
    }

 		virtual QCString trNamespaceIndex()
      // This is used in LaTeX as the title of the chapter with the 
      // index of all namespaces.
    { return "���ֿռ�����"; }

 		virtual QCString trNamespaceDocumentation()
      // This is used in LaTeX as the title of the chapter containing
      // the documentation of all namespaces.
    { return "���ֿռ��ĵ�"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

    /*! This is used in the documentation before the list of all
     *  namespaces in a file.
     */
 		virtual QCString trNamespaces()
    {
      // return "Namespaces";
      return "���ֿռ�";
    }

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
   		QCString result=(QCString)"��";
      switch(compType)
      {
        case ClassDef::Class:      result+="��"; break;
        case ClassDef::Struct:     result+="�ṹ"; break;
        case ClassDef::Union:      result+="����"; break;
        case ClassDef::Interface:  result+="�ӿ�"; break;
        case ClassDef::Protocol:   result+="Э��"; break;
        case ClassDef::Category:   result+="����"; break;
        case ClassDef::Exception:  result+="�쳣"; break;
      }
      result+="���ĵ��������ļ����ɣ�";
      return result;
    }

    /*! This is in the (quick) index as a link to the alphabetical compound
     * list.
     */
 		virtual QCString trAlphabeticalList()
    { return "���ֵ�˳��������б�"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the heading text for the retval command. */
 		virtual QCString trReturnValues()
    { return "����ֵ"; }

    /*! This is in the (quick) index as a link to the main page (index.html)
     */
 		virtual QCString trMainPage()
    { return "��ҳ"; }

    /*! This is used in references to page that are put in the LaTeX 
     *  documentation. It should be an abbreviation of the word page.
     */
 		virtual QCString trPageAbbreviation()
    { return "p."; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991106
//////////////////////////////////////////////////////////////////////////

                virtual QCString trDefinedAtLineInSourceFile()
    {
      return "���ļ�"CN_SPC"@1"CN_SPC"��"CN_SPC"@0"CN_SPC"�ж��塣";
    }

 		virtual QCString trDefinedInSourceFile()
    {
      return "���ļ�"CN_SPC"@0"CN_SPC"�ж��塣";
    }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991205
//////////////////////////////////////////////////////////////////////////

 		virtual QCString trDeprecated()
    {
      return "Deprecated";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

    /*! this text is put before a collaboration diagram */
 		virtual QCString trCollaborationDiagram(const char *clName)
    {
      return (QCString)clName+CN_SPC"����ͼ��";
    }

    /*! this text is put before an include dependency graph */
 		virtual QCString trInclDepGraph(const char *fName)
    {
      return (QCString)fName+CN_SPC"����/������ϵͼ��";
    }

    /*! header that is put before the list of constructor/destructors. */
 		virtual QCString trConstructorDocumentation()
    {
      return "���켰���������ĵ�"; 
    }

    /*! Used in the file documentation to point to the corresponding sources. */
 		virtual QCString trGotoSourceCode()
    {
      return "������ļ���Դ���롣";
    }

    /*! Used in the file sources to point to the corresponding documentation. */
 		virtual QCString trGotoDocumentation()
    {
      return "������ļ����ĵ���";
    }

    /*! Text for the \\pre command */
 		virtual QCString trPrecondition()
    {
      return "ǰ������";
    }

    /*! Text for the \\post command */
 		virtual QCString trPostcondition()
    {
      return "��������";
    }

    /*! Text for the \\invariant command */
 		virtual QCString trInvariant()
    {
      return "������";
    }

    /*! Text shown before a multi-line variable/enum initialization */
 		virtual QCString trInitialValue()
    {
      return "��ʼ�����У�";
    }

    /*! Text used the source code in the file index */
 		virtual QCString trCode()
    {
      return "����";
    }

 		virtual QCString trGraphicalHierarchy()
    {
      return "��̳й�ϵͼ";
    }

 		virtual QCString trGotoGraphicalHierarchy()
    {
      return "�����̳й�ϵͼ";
    }

 		virtual QCString trGotoTextualHierarchy()
    {
      return "�����̳й�ϵ��";
    }

 		virtual QCString trPageIndex()
    {
      return "ҳ������";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////
    
 		virtual QCString trNote()
    {
      return "ע��";
    }

 		virtual QCString trPublicTypes()
    {
      return "��������";
    }

 		virtual QCString trPublicAttribs()
    {
			 if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
			 { 
				 return "���ݳ�Ա";
			 }
			 else {
				 return "��������";
			 }
    }

 		virtual QCString trStaticPublicAttribs()
    {
      return "��̬��������";
    }

 		virtual QCString trProtectedTypes()
    {
      return "��������";
    }

 		virtual QCString trProtectedAttribs()
    {
      return "��������";
    }

 		virtual QCString trStaticProtectedAttribs()
    {
      return "��̬��������";
    }

 		virtual QCString trPrivateTypes()
    {
      return "˽������";
    }

 		virtual QCString trPrivateAttribs()
    {
      return "˽������";
    }

 		virtual QCString trStaticPrivateAttribs()
    {
      return "��̬˽������";
    }


//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a todo item */
 		virtual QCString trTodo()
    {
      return "TODO";
    }

    /*! Used as the header of the todo list */
 		virtual QCString trTodoList()
    {
      return "TODO"CN_SPC"�б�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

 		virtual QCString trReferencedBy()
    {
      return "�ο���";
    }

 		virtual QCString trRemarks()
    {
      return "����";
    }

 		virtual QCString trAttention()
    {
      return "ע��";
    }

 		virtual QCString trInclByDepGraph()
    {
      return "��ͼչʾֱ�ӻ��Ӱ������ļ����ļ���";
    }

 		virtual QCString trSince()
    {
      return "�Դ�";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

    /*! title of the graph legend page */
 		virtual QCString trLegendTitle()
    {
      return "ͼ��";
    }

    /*! page explaining how the dot graph's should be interpreted */
 		virtual QCString trLegendDocs()
    {
      return 
        "��ҳ����չʾ��������"CN_SPC"Doxygen"CN_SPC"���ɵ�ͼ�Ρ�<p>\n"
        "�뿼������ʾ����\n"
        "\\code\n"
        "/*! ���ڽ�ȡ��ʹ���಻�ɼ� */\n"
        "class Invisible { };\n\n"
        "/*! ����ȡ���࣬�̳й�ϵ������������ */\n"
        "class Truncated : public Invisible { };\n\n"
        "/* û�б�"CN_SPC"doxygen"CN_SPC"��ע���ĵ������� */\n"
        "class Undocumented { };\n\n"
        "/*! �����м̳е��� */\n"
        "class PublicBase : public Truncated { };\n\n"
        "/*! A template class */\n"
        "template<class T> class Templ { };\n\n"
        "/*! �������̳е��� */\n"
        "class ProtectedBase { };\n\n"
        "/*! ��˽�м̳е��� */\n"
        "class PrivateBase { };\n\n"
        "/*! ��ʹ�õ��� */\n"
        "class Used { };\n\n"
        "/*! �̳���������������� */\n"
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
        "����������ļ���ָ����"CN_SPC"MAX_DOT_GRAPH_HEIGHT"CN_SPC"��ֵΪ200��"
        "��Doxygen���������µ�ͼ�Σ�"
        "<p><center><img src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
        "<p>\n"
        "����ͼ���еľ��������µĺ��壺\n"
        "<ul>\n"
        "<li>����ɫ���ľ��δ���ǰ�����ṹ��\n"
        "<li>��ɫ�߿�ľ��δ���<i>�ĵ���</i>�����ṹ��\n"
        "<li>��ɫ�߿�ľ��δ���û��<i>�ĵ���</i>�����ṹ��\n"
        "<li>��ɫ�߿�ľ��δ���̳�/������ϵû�б�������ʾ�������ṹ�����һ��ͼ��ĳ�"
        "�����ָ���ߴ磬��������ȡ��"
        "</ul>\n"
        "������ͷ�����µĺ��壺\n"
        "<ul>\n"
        "<li>����ɫ�ļ�ͷ������ʾ������֮��Ĺ��м̳й�ϵ��\n"
        "<li>����ɫ�ļ�ͷ������ʾ�����̳й�ϵ��\n"
        "<li>���ɫ�ļ�ͷ������ʾ˽�м̳й�ϵ��\n"
        "<li>��ɫ��״�����ļ�ͷ������ʾ������֮���������ʹ�õĹ�ϵ��ͨ����ͷ�Աߵı�������"
        "���ʵ���ͷ��ָ�����ṹ��\n"
        "</ul>\n";
    }
    /*! text for the link to the legend page */
 		virtual QCString trLegend()
    {
      return "ͼ��";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a test item */
    virtual QCString trTest()
    {
      return "����";
    }

    /*! Used as the header of the test list */
    virtual QCString trTestList()
    {
      return "�����б�";
    }

//////////////////////////////////////////////////////////////////////////
//// new since 1.2.1
////////////////////////////////////////////////////////////////////////////
		/*! Used as a section header for KDE-2 IDL methods */
		virtual QCString trDCOPMethods()
		{
			return "DCOP"CN_SPC"����";
		}

//////////////////////////////////////////////////////////////////////////
//// new since 1.2.2
////////////////////////////////////////////////////////////////////////////

		/*! Used as a section header for IDL properties */
		virtual QCString trProperties()
		{
			return "����";
		}

		/*! Used as a section header for IDL property documentation */
		virtual QCString trPropertyDocumentation()
		{
			return "�����ĵ�";
		}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

    /*! Used for Java classes in the summary section of Java packages */
    virtual QCString trClasses()
    {
			if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
			{
				return "���ݽṹ";
			}
			else
			{
				return "��";
			}
    }

    /*! Used as the title of a Java package */
    virtual QCString trPackage(const char *name)
    {
      return (QCString)"�� "+name;
    }
		
    /*! Title of the package index page */
    virtual QCString trPackageList()
    {
      return "���б�";
    }

    /*! The description of the package index page */
    virtual QCString trPackageListDescription()
    {
			 return "�����г����еİ���������Ҫ˵��(����еĻ�)��"; 
    }

    /*! The link name in the Quick links header for each page */
    virtual QCString trPackages()
    {
      return "��";
    }

    /*! Text shown before a multi-line define */
    virtual QCString trDefineValue()
    {
      return 	"ֵ:";
    }

////////////////////////////////////////////////////////////////////////////
//// new since 1.2.6
////////////////////////////////////////////////////////////////////////////
		virtual QCString trBug ()
		{
			return "ȱ��";
		}

		virtual QCString trBugList ()
		{
			return "ȱ���б�";
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
      return "936";
    }

    /*! Used as ansicpg for RTF fcharset 
     *  \see trRTFansicp() for a table of possible values.
     */
    virtual QCString trRTFCharSet()
    {
      return "134";
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
    virtual QCString trClass(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "Class" : "class"));
      if (!singular)  result+="es";
      return result; 
			*/
			return "��";
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trFile(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "File" : "file"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "�ļ�";

    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trNamespace(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "Namespace" : "namespace"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "���ֿռ�";
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGroup(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "Group" : "group"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "��";
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trPage(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "Page" : "page"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "ҳ";
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trMember(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "Member" : "member"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "��Ա";
    }
   
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGlobal(bool /*first_capital*/, bool /*singular*/)
    { 
			/*
   		QCString result((first_capital ? "Global" : "global"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "ȫ�ֶ���";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

    /*! This text is generated when the \\author command is used and
     *  for the author section in man pages. */
    virtual QCString trAuthor(bool /*first_capital*/, bool /*singular*/)
    {                                                                         
			/*
   		QCString result((first_capital ? "Author" : "author"));
      if (!singular)  result+="s";
      return result; 
			*/
			return "����";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

    /*! This text is put before the list of members referenced by a member
     */
    virtual QCString trReferences()
    {
      return "�ο�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

    /*! used in member documentation blocks to produce a list of 
     *  members that are implemented by this one.
     */
    virtual QCString trImplementedFromList(int numEntries)
    {
      /* return "Implements "+trWriteList(numEntries)+"."; */
      return "ʵ����"CN_SPC+trWriteList(numEntries)+"��";
    }

    /*! used in member documentation blocks to produce a list of
     *  all members that implement this abstract member.
     */
    virtual QCString trImplementedInList(int numEntries)
    {
      /* return "Implemented in "+trWriteList(numEntries)+"."; */
      return "��"CN_SPC+trWriteList(numEntries)+CN_SPC"�ڱ�ʵ�֡�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

    /*! used in RTF documentation as a heading for the Table
     *  of Contents.
     */
    virtual QCString trRTFTableOfContents()
    {
      /* return "Table of Contents"; */
      return "Ŀ¼";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

    /*! Used as the header of the list of item that have been 
     *  flagged deprecated 
     */
    virtual QCString trDeprecatedList()
    {
/*    return "Deprecated List";  */
      return "��ʱ�б�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.18
//////////////////////////////////////////////////////////////////////////

    /*! Used as a header for declaration section of the events found in 
     * a C# program
     */
    virtual QCString trEvents()
    {
      /*      return "Events"; */
      return "�¼�";
    }
    /*! Header used for the documentation section of a class' events. */
    virtual QCString trEventDocumentation()
    {
      /* return "Event Documentation"; */
      return "�¼��ĵ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a heading for a list of Java class types with package scope.
     */
    virtual QCString trPackageTypes()
    { 
      /* return "Package Types"; */
      return "ģ������";
    }
    /*! Used as a heading for a list of Java class functions with package 
     * scope. 
     */
    virtual QCString trPackageMembers()
    { 
      /* return "Package Functions"; */
      return "ģ�麯��";
    }
    /*! Used as a heading for a list of static Java class functions with 
     *  package scope.
     */
    virtual QCString trStaticPackageMembers()
    { 
      /* return "Static Package Functions"; */
      return "��̬ģ�麯��";
    }
    /*! Used as a heading for a list of Java class variables with package 
     * scope.
     */
    virtual QCString trPackageAttribs()
    { 
      /* return "Package Attributes"; */
      return "ģ������";
    }
    /*! Used as a heading for a list of static Java class variables with 
     * package scope.
     */
    virtual QCString trStaticPackageAttribs()
    { 
      /* return "Static Package Attributes"; */
      return "��̬ģ������";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.3.1
//////////////////////////////////////////////////////////////////////////

    /*! Used in the quick index of a class/file/namespace member list page 
     *  to link to the unfiltered list of all members.
     */
    virtual QCString trAll()
    {
      /* return "All"; */
      return "ȫ��";
    }
    /*! Put in front of the call graph for a function. */
    virtual QCString trCallGraph()
    {
      /* return "Here is the call graph for this function:"; */
      return "��������ͼ:";
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
      /* return "Search for"; */
      return "����";
    }
    /*! This string is used as the title for the page listing the search
     *  results.
     */
    virtual QCString trSearchResultsTitle()
    {
      /* return "Search Results"; */
      return "�������";
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
        /* return "Sorry, no documents matching your query."; */
        return "�Բ����Ҳ�������Ĳ�ѯ������ĵ���";
      }
      else if (numDocuments==1)
      {
        /* return "Found <b>1</b> document matching your query."; */
        return "�ҵ�<b>1</b>ƪ����Ĳ�ѯ������ĵ���";
      }
      else 
      {
        /* return "Found <b>$num</b> documents matching your query. "
               "Showing best matches first."; */
        return "�ҵ�<b>$num</b>ƪ����Ĳ�ѯ������ĵ���"
               "����ʾ���Ǻϵ��ĵ���";
      }
    }
    /*! This string is put before the list of matched words, for each search 
     *  result. What follows is the list of words that matched the query.
     */
    virtual QCString trSearchMatches()
    {
      /* return "Matches:"; */
      return "���ϵĽ��:";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.8
//////////////////////////////////////////////////////////////////////////

    /*! This is used in HTML as the title of page with source code for file filename
     */
    virtual QCString trSourceFile(QCString& filename)
    {
      /* return filename + " Source File"; */
      return filename + CN_SPC"Դ�ļ�";
    }
//////////////////////////////////////////////////////////////////////////
// new since 1.3.9
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the name of the chapter containing the directory
     *  hierarchy.
     */
    virtual QCString trDirIndex()
    /*     { return "Directory Hierarchy"; } */
    {
      return "Ŀ¼�ṹ";
    }

    /*! This is used as the name of the chapter containing the documentation
     *  of the directories.
     */
    virtual QCString trDirDocumentation()
    /*     { return "Directory Documentation"; } */
    {
      return "Ŀ¼�ĵ�";
    }

    /*! This is used as the title of the directory index and also in the
     *  Quick links of a HTML page, to link to the directory hierarchy.
     */
    virtual QCString trDirectories()
    /*     { return "Directories"; } */
    {
      return "Ŀ¼";
    }

    /*! This returns a sentences that introduces the directory hierarchy. 
     *  and the fact that it is sorted alphabetically per level
     */
    virtual QCString trDirDescription()
/*     { return "This directory hierarchy is sorted roughly, " */
/*              "but not completely, alphabetically:"; */
/*     } */
    {
      return "Ŀ¼�ṹ���������Ե�����";
    }

    /*! This returns the title of a directory page. The name of the
     *  directory is passed via \a dirName.
     */
    virtual QCString trDirReference(const char *dirName)
    /*     { QCString result=dirName; result+=" Directory Reference"; return result; } */
    {
      QCString result=dirName;
      result+=CN_SPC"Ŀ¼�ο�"; 
      return result;
    }

    /*! This returns the word directory with or without starting capital
     *  (\a first_capital) and in sigular or plural form (\a singular).
     */
    virtual QCString trDir(bool, bool)
    { 
      /*       QCString result((first_capital ? "Director" : "director")); */
      /*       if (singular) result+="y"; else result+="ies"; */
      /*       return result;  */
      return "Ŀ¼";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.4.1
//////////////////////////////////////////////////////////////////////////

    /*! This text is added to the documentation when the \\overload command
     *  is used for a overloaded function.
     */
    virtual QCString trOverloadText()
    {
       /* return "This is an overloaded member function, "
              "provided for convenience. It differs from the above "
              "function only in what argument(s) it accepts."; */
      return "����Ϊ����ʹ�ö��ṩ��һ�����س�Ա������"
             "������ĺ�����ȣ������ܲ�ͬ���͵Ĳ�����";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.4.6
//////////////////////////////////////////////////////////////////////////

    /*! This is used to introduce a caller (or called-by) graph */
    virtual QCString trCallerGraph()
    {
      /* return "Here is the caller graph for this function:"; */
      return "������������ĵ���ͼ��";
    }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for enumeration values
     */
    virtual QCString trEnumerationValueDocumentation()
    { 
      /* return "Enumerator Documentation"; */
      return "ö�ٱ����ĵ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.5.4 (mainly for Fortran)
//////////////////////////////////////////////////////////////////////////
    
    /*! header that is put before the list of member subprograms (Fortran). */
    virtual QCString trMemberFunctionDocumentationFortran()
    // { return "Member Function/Subroutine Documentation"; }
    { return "��Ա�����������ĵ�"; }

    /*! This is put above each page as a link to the list of annotated data types (Fortran). */    
    virtual QCString trCompoundListFortran()
    // { return "Data Types List"; }
    { return "���������б�"; }

    /*! This is put above each page as a link to all members of compounds (Fortran). */
    virtual QCString trCompoundMembersFortran()
    // { return "Data Fields"; }
    { return "������"; }

    /*! This is an introduction to the annotated compound list (Fortran). */
    virtual QCString trCompoundListDescriptionFortran()
    // { return "Here are the data types with brief descriptions:"; }
    { return "����Ҫ���������������б�:"; }

    /*! This is an introduction to the page with all data types (Fortran). */
    virtual QCString trCompoundMembersDescriptionFortran(bool extractAll)
    {
    //   QCString result="Here is a list of all ";
    //   if (!extractAll)
    //   {
    //     result+="documented ";
    //   }
    //   result+="data types members";
    //   result+=" with links to ";
    //   if (!extractAll) 
    //   {
    //      result+="the data structure documentation for each member";
    //   }
    //   else 
    //   {
    //      result+="the data types they belong to:";
    //   }
    //   return result;
      if(!extractAll) {
        return "���������ĵ����������ͳ�Ա�б����е�ÿ����Ա�����ݽṹ�ĵ�������";
      } else {
        return "�������������ͳ�Ա�б����е���Ա�������������͵�����:";
      }

    }

    /*! This is used in LaTeX as the title of the chapter with the 
     * annotated compound index (Fortran).
     */
    virtual QCString trCompoundIndexFortran()
    // { return "Data Type Index"; }
    { return "������������"; }


    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all data types (Fortran).
     */
    virtual QCString trTypeDocumentation()
    // { return "Data Type Documentation"; }
    { return "���������ĵ�"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) subprograms (Fortran).
     */
    virtual QCString trSubprograms()
    //{ return "Functions/Subroutines"; }
    { return "����/����"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for subprograms (Fortran)
     */
    virtual QCString trSubprogramDocumentation()
    //{ return "Function/Subroutine Documentation"; }
    { return "����/�����ĵ�"; }


    /*! This is used in the documentation of a file/namespace/group before 
     *  the list of links to documented compounds (Fortran)
     */
     virtual QCString trDataTypes()
    // { return "Data Types"; }
    { return "��������"; }
    
    /*! used as the title of page containing all the index of all modules (Fortran). */
    virtual QCString trModulesList()
    // { return "Modules List"; }
    { return "ģ���б�"; }

    /*! used as an introduction to the modules list (Fortran) */
    virtual QCString trModulesListDescription(bool extractAll)
    {
      // QCString result="Here is a list of all ";
      // if (!extractAll) result+="documented ";
      // result+="modules with brief descriptions:";
      // return result;
      if(!extractAll) {
        return "����Ҫ���������ĵ���ģ���б�:";
      } else {
        return "����Ҫ������ģ���б�:";
      }
    }

    /*! used as the title of the HTML page of a module/type (Fortran) */
    virtual QCString trCompoundReferenceFortran(const char *clName,
                                    ClassDef::CompoundType compType,
                                    bool isTemplate)
    {
      // QCString result=(QCString)clName;
      // switch(compType)
      // {
      //   case ClassDef::Class:      result+=" Module"; break;
      //   case ClassDef::Struct:     result+=" Type"; break;
      //   case ClassDef::Union:      result+=" Union"; break;
      //   case ClassDef::Interface:  result+=" Interface"; break;
      //   case ClassDef::Protocol:   result+=" Protocol"; break;
      //   case ClassDef::Category:   result+=" Category"; break;
      //   case ClassDef::Exception:  result+=" Exception"; break;
      // }
      // if (isTemplate) result+=" Template";
      // result+=" Reference";
      // return result;
      QCString result=(QCString)clName;
      switch(compType)
      {
        case ClassDef::Class:      result+=CN_SPC"ģ��"; break;
        case ClassDef::Struct:     result+=CN_SPC"����"; break;
        case ClassDef::Union:      result+=CN_SPC"����"; break;
        case ClassDef::Interface:  result+=CN_SPC"����"; break;
        case ClassDef::Protocol:   result+=CN_SPC"�ӿ�"; break;
        case ClassDef::Category:   result+=CN_SPC"Ŀ¼"; break;
        case ClassDef::Exception:  result+=CN_SPC"�쳣"; break;
      }
      if (isTemplate) result+="ģ��";
      result+="�ο��ֲ�";
      return result;
    }
    /*! used as the title of the HTML page of a module (Fortran) */
    virtual QCString trModuleReference(const char *namespaceName)
    {
      QCString result=namespaceName;
      // result+=" Module Reference";        
      result += CN_SPC"ģ��ο��ֲ�";
      return result;
    }
    
    /*! This is put above each page as a link to all members of modules. (Fortran) */
    virtual QCString trModulesMembers()
    // { return "Module Members"; }
    { return "ģ���Ա"; }

    /*! This is an introduction to the page with all modules members (Fortran) */
    virtual QCString trModulesMemberDescription(bool extractAll)
    { 
      // QCString result="Here is a list of all ";
      // if (!extractAll) result+="documented ";
      // result+="module members with links to ";
      // if (extractAll) 
      // {
      //   result+="the module documentation for each member:";
      // }
      // else 
      // {
      //   result+="the modules they belong to:";
      // }
      // return result;
      if(!extractAll) {
        return "���������ĵ���ģ���Ա�б����е�ÿ����Ա����ģ����ĵ�������";
      } else {
        return "������ģ���Ա�б����е���Ա������ģ�������:";
      }
    }

    /*! This is used in LaTeX as the title of the chapter with the 
     *  index of all modules (Fortran).
     */
    virtual QCString trModulesIndex()
    // { return "Modules Index"; }
    { return "ģ������"; }
    
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trModule(bool, bool)
    {       
      // QCString result((first_capital ? "Module" : "module"));
      // if (!singular)  result+="s";
      // return result; 
      return "ģ��";
    }
    /*! This is put at the bottom of a module documentation page and is
     *  followed by a list of files that were used to generate the page.
     */
    virtual QCString trGeneratedFromFilesFortran(ClassDef::CompoundType compType,
        bool)
    { // here s is one of " Module", " Struct" or " Union"
      // single is true implies a single file
      // QCString result=(QCString)"The documentation for this ";
      // switch(compType)
      // {
      //   case ClassDef::Class:      result+="module"; break;
      //   case ClassDef::Struct:     result+="type"; break;
      //   case ClassDef::Union:      result+="union"; break;
      //   case ClassDef::Interface:  result+="interface"; break;
      //   case ClassDef::Protocol:   result+="protocol"; break;
      //   case ClassDef::Category:   result+="category"; break;
      //   case ClassDef::Exception:  result+="exception"; break;
      // }
      // result+=" was generated from the following file";
      // if (single) result+=":"; else result+="s:";
      // return result;
      QCString result="��";
      switch(compType)
      {
        case ClassDef::Class:      result+=CN_SPC"ģ��"; break;
        case ClassDef::Struct:     result+=CN_SPC"����"; break;
        case ClassDef::Union:      result+=CN_SPC"����"; break;
        case ClassDef::Interface:  result+=CN_SPC"����"; break;
        case ClassDef::Protocol:   result+=CN_SPC"�ӿ�"; break;
        case ClassDef::Category:   result+=CN_SPC"Ŀ¼"; break;
        case ClassDef::Exception:  result+=CN_SPC"�쳣"; break;
      }
      result+="���ĵ��������ļ�����:";
      return result;
    }
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trType(bool, bool)
    { 
      return "����";
    }
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trSubprogram(bool, bool)
    { 
      return "�ӳ���";
    }

    /*! C# Type Constraint list */
    virtual QCString trTypeConstraints()
    {
      return "��������";
    }
};

#endif

